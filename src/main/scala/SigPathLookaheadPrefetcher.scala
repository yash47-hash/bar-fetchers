/* --------------------------------------------

Author: Yashwant Kumar Balivada

J. Kim, S. H. Pugsley, P. V. Gratz, A. L. N. Reddy, C. Wilkerson and Z. Chishti, 
"Path confidence based lookahead prefetching," 2016 49th Annual IEEE/ACM International Symposium on Microarchitecture (MICRO), 
Taipei, Taiwan, 2016, pp. 1-12, doi: 10.1109/MICRO.2016.7783763.
-----------------------------------------------*/


package barf

import chisel3._
import chisel3.util._
import chisel3.experimental._
import org.chipsalliance.cde.config.{Field, Parameters}
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.util._
import freechips.rocketchip.tile._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.subsystem.{CacheBlockBytes}
import freechips.rocketchip.util.WideCounter

case class SigPathPrefetcher(
    st_depth: Int = 256,            //Signature Table Depth.
    pht_depth: Int = 512,           //Pattern History Table Depth.
    blk_bits: Int = 6,              //Prefetching in blocks.
    pref_threshold: Double = 0.25,  //Prefetch Confidence Threshold 
) extends CanInstantiatePrefetcher {
    override def desc = "SigPathPrefetcher"
    def instantiate()(implicit p: Parameters) = Module(new SigPathlookaheadPrefetcher(this)(p))
}

class SigPathlookaheadPrefetcher(params: SigPathPrefetcher) (implicit p: Parameters) extends AbstractPrefetcher()(p){
    val st_pages = log2Ceil(params.st_depth)
    val pht_signatures = log2Ceil(params.pht_depth)

    val pageNum = Reg(UInt()) //io.snoop.bits.block >> (params.blk_bits)
    val blockAddr = Reg(UInt()) //pageNum << (params.blk_bits)
    val pageOffset = Reg(UInt()) //io.snoop.bits.block(params.blk_bits - 1, 0)
    val regSignature = RegInit(0.U(9.W))
    val phtSigns = RegInit(0.U(9.W))
    val regDelta = RegInit(0.S(7.W))
    val pFDelta = RegInit(0.S(7.W))
    val sigConfidence      = RegInit(0.U(9.W))
    val prevSigConfidence = RegInit(0.U(9.W))   
    val patternThreshold  = (params.pref_threshold * 256).toInt.U(8.W)        
    val totalPrefetches = RegInit(0.U(10.W))
    val usefulCntr = RegInit(0.U(10.W))
    val s_idle :: s_compute :: s_lookahead :: s_confidence :: s_lowconfidence :: Nil = Enum(5)
    val st_idle :: st_compare :: st_update :: st_prefetch :: Nil = Enum(4)
    val state = RegInit(s_idle)
    val st_state = RegInit(st_idle)
    val currPagePrefetch = Reg(UInt())

    //ST, PhT, prefetch queue & io.request, also need to fix confidence parameters, GHR, Prefetch Filter, throttle

    val ptAccessArry_cntr = RegInit(
        VecInit(Seq.fill(params.st_depth)(0.U(3.W)))
    )

    val prefetchAddr = RegInit(0.U(64.W))

    val signature_table = RegInit(VecInit(Seq.fill(params.st_depth) {
        val entry = Wire(new SignatureTableEntries())
        entry.pageTag := 0.U
        entry.last_offset := 0.U
        entry.signature.patternSign := 0.U
        entry.signature.signDelta := 0.S
        entry.prefetched_entries := 0.U
        entry
    }))

    val pht_table = RegInit(VecInit(Seq.tabulate(params.pht_depth) { j =>
        val pht_entry = Wire(new PatternHistoryTableEntries())
        pht_entry.sig_idx := (j + 1).U
        pht_entry.c_sig   := 0.U
        pht_entry.delta_table.foreach { d =>
            d.delta   := 0.S
            d.c_delta := 0.U
        }
        pht_entry
    }))

    val divisionValues = for (n <- 0 until 16) yield {
        for (d <- 0 until 16) yield {
            if (d == 0) 0.U(8.W) // Handle division by zero
            else {
                val result = (n.toDouble / d.toDouble * 256).toInt
                if (result > 255) 255.U(8.W) else result.U(8.W)
            }
        }
    }

    val divisionValuesThrottling = for (n <- 0 until 1024) yield {
        for (d <- 0 until 1024) yield {
            if (d == 0) 0.U(20.W) // Handle division by zero
            else {
                val result = (n.toDouble / d.toDouble * 1024).toInt
                if (result > 1023) 1023.U(20.W) else result.U(20.W)
            }
        }
    }

    val globalHistoryREG = RegInit(VecInit(Seq.fill(8) {
        val gEntry = Wire(new GlobalHistoryRegister())
        gEntry.sigEntry := 0.U
        gEntry.sigConf := 0.U
        gEntry.pageBoundaryLastOffset := 0.U
        gEntry.lastDelta := 0.S
        gEntry.lru := 0.U
        gEntry
    }))

    val flatData = divisionValues.flatten 
    val divisionLut = VecInit(flatData)
    val divideIdx = Reg(UInt())

    val flatDataTrottle = divisionValuesThrottling.flatten 
    val divisionLutTrottle = VecInit(flatDataTrottle)

    val chunks = pageNum.asTypeOf(Vec(20 / log2Up(params.st_depth), UInt(log2Up(params.st_depth).W)))
    val indexSigTable = chunks.reduce(_ ^ _)
    //val indexSigTable = pageNum%params.st_depth.U 
    val offset_ST = Reg(SInt())
    val phtSigTag = Reg(UInt())
    val phtSigDel = Reg(SInt())

    val ghrOffset = RegInit(0.U(8.W))
    val ghrtempOffset = RegInit(0.S(8.W))
    val offsetKey = Reg(UInt())

    val ghrSearchforOffset = VecInit(Seq.tabulate(8) { i =>
        ghrtempOffset := globalHistoryREG(i).pageBoundaryLastOffset.zext.asSInt + globalHistoryREG(i).lastDelta
        when(ghrtempOffset > 0.S){
            offsetKey := (ghrtempOffset - 64.S).asUInt
        } .otherwise {
            offsetKey := (64.S + ghrtempOffset).asUInt
        }
        offsetKey === pageOffset
    })

    val ghrOffsetHit = ghrSearchforOffset.reduce(_||_)
    val ghrOffsetHitPos = PriorityEncoder(ghrSearchforOffset) 

    val pref_out = Reg(Output(Flipped(Decoupled(new prefetch_reqSPP))))
    val queue_out = Reg(Input(Flipped(Decoupled(new prefetch_reqSPP))))
    val prefetch_active = RegInit(false.B)
    val reset_deq = RegInit(true.B) 
    val prefetch_queue = Module(new Queue(new prefetch_reqSPP, entries=8, flow=true))
    val tempPtaccess = WireInit(0.U(3.W))
    val baseAddr = Reg(UInt(32.W))

    val currSig = Reg(UInt(9.W))
    val lookaheadConf = RegInit(0.U(8.W))
    val prevConf = RegInit(255.U(8.W))
    val currBlock_offset = RegInit(0.U(7.W))
    val prefDelta = RegInit(0.S(7.W))
    val crossPageBoundary = RegInit(false.B)
    val divideIdxTrottle = Cat(usefulCntr, totalPrefetches)
    val throttlePrefetcher = divisionLutTrottle(divideIdxTrottle)

    pref_out.valid := false.B
    prefetch_queue.io.deq.ready := false.B
    prefetch_queue.io.enq.valid := false.B
    prefetch_queue.io.enq.bits.addr := RegInit(0.U(64.W))
    prefetch_queue.io.enq.bits.write := RegInit(0.U(1.W))

    when(io.snoop.valid && ((signature_table(indexSigTable).prefetched_entries & (1.U<<pageOffset)) =/= 0.U)){
        usefulCntr := usefulCntr + 1.U
    }

    when(st_state === st_idle){
        when(io.snoop.valid){
            pageNum := io.snoop.bits.block >> (params.blk_bits)
            blockAddr := io.snoop.bits.block_address
            pageOffset := io.snoop.bits.block(params.blk_bits - 1, 0)
            st_state := st_compare
        }
    }.elsewhen(st_state === st_compare){
        when(signature_table(indexSigTable).pageTag === pageNum && ptAccessArry_cntr(indexSigTable) >= 2.U){
            when((currPagePrefetch =/= pageNum) | (state === s_lowconfidence)){
                state := s_idle
                baseAddr := blockAddr
                currBlock_offset := pageOffset
                phtSigTag := signature_table(indexSigTable).signature.patternSign
                phtSigDel := (pageOffset.zext - signature_table(indexSigTable).last_offset.zext).asSInt
                prevConf := 196.U
            }
            offset_ST := (pageOffset - signature_table(indexSigTable).last_offset).asSInt
            signature_table(indexSigTable).signature.patternSign := (signature_table(indexSigTable).signature.patternSign << 3) ^ (pageOffset.zext - signature_table(indexSigTable).last_offset.zext).asUInt
            signature_table(indexSigTable).signature.signDelta := (pageOffset.zext - signature_table(indexSigTable).last_offset.zext).asSInt
            signature_table(indexSigTable).last_offset := pageOffset
            signature_table(indexSigTable).prefetched_entries := signature_table(indexSigTable).prefetched_entries | (1.U<<pageOffset)
            st_state := st_update
        } .otherwise {
            st_state := st_idle
            when(currPagePrefetch =/= pageNum){
                state := s_idle
            }
            when(signature_table(indexSigTable).pageTag =/= pageNum){
                signature_table(indexSigTable).pageTag := pageNum
                ptAccessArry_cntr(indexSigTable) := 0.U
                signature_table(indexSigTable).prefetched_entries := 0.U
            } .otherwise {
                ptAccessArry_cntr(indexSigTable) := ptAccessArry_cntr(indexSigTable) + 1.U
                signature_table(indexSigTable).prefetched_entries := signature_table(indexSigTable).prefetched_entries | (1.U<<pageOffset)
            } 
            
            updatePht(signature_table(indexSigTable).signature.patternSign, (pageOffset.zext - signature_table(indexSigTable).last_offset.zext).asSInt) // UPdating PhT
    
            signature_table(indexSigTable).signature.patternSign := (signature_table(indexSigTable).signature.patternSign << 3) ^ (pageOffset - signature_table(indexSigTable).last_offset).asUInt
            signature_table(indexSigTable).signature.signDelta := (pageOffset.zext - signature_table(indexSigTable).last_offset.zext).asSInt
            signature_table(indexSigTable).last_offset := pageOffset
            when(ghrOffsetHit){
                val ghrSignature = globalHistoryREG(ghrOffsetHitPos).sigEntry
                val ghrDelta = globalHistoryREG(ghrOffsetHitPos).lastDelta

                when(globalHistoryREG(ghrOffsetHitPos).sigConf >= patternThreshold){
                    st_state := st_update
                    baseAddr := blockAddr
                    currBlock_offset := pageOffset
                    phtSigTag := ghrSignature
                    phtSigDel := ghrDelta
                    prevConf := 196.U
                }
                globalHistoryREG(ghrOffsetHitPos).lru := globalHistoryREG(ghrOffsetHitPos).lru + 1.U
            }
        }
    }.elsewhen (st_state === st_update){
        updatePht(phtSigTag,phtSigDel)
        currSig := phtSigTag
        prefDelta := phtSigDel
        currPagePrefetch := pageNum
        st_state := st_prefetch
    }.elsewhen (st_state === st_prefetch){
        st_state := st_idle
        state := s_compute
    }

    when(state === s_idle){
        //When SPP is idle.
    } .elsewhen(state === s_compute) {
        currSig := ((currSig << 3) ^ prefDelta(params.blk_bits-1,0))(log2Up(params.pht_depth)-1,0)
        val cDeltas = pht_table(currSig).delta_table.map(_.c_delta)
        val maxCDelta = cDeltas.reduce((a, b) => Mux(a > b, a, b))
        val highConfIdx = PriorityEncoder(cDeltas.map(_ === maxCDelta))
        prefDelta := pht_table(currSig).delta_table(highConfIdx).delta
        divideIdx := Cat(pht_table(currSig).delta_table(highConfIdx).c_delta, pht_table(currSig).c_sig)
        state := s_confidence
    } .elsewhen(state === s_confidence){
        when(totalPrefetches>500.U){
            lookaheadConf := callookaheadConfidence(throttlePrefetcher,prevConf,divisionLut(divideIdx)) //throttlePrefetcher*prevConf*(divisionLut(divideIdx)) //Trottling the prefetcher
        } .otherwise {
            lookaheadConf := callookaheadConfidence(1023.U(10.W),prevConf,divisionLut(divideIdx)) //No throttle till 20 prefetches
        }
        crossPageBoundary := Mux(((currBlock_offset.asSInt+prefDelta>63.S) || (currBlock_offset.asSInt+prefDelta<0.S)), true.B, false.B)
        state := s_lookahead
    } .elsewhen(state === s_lookahead){
        prevConf := Mux(lookaheadConf === 0.U, 128.U(8.W), lookaheadConf)
        when(!crossPageBoundary && lookaheadConf>=patternThreshold){
            val w = baseAddr.getWidth
            val addrToPrefetch = (baseAddr.zext.asSInt + (prefDelta<<log2Up(io.snoop.bits.blockBytes))).asUInt(w-1,0)
            baseAddr := addrToPrefetch
            currBlock_offset := (currBlock_offset.asSInt+prefDelta).asUInt
            when((signature_table(indexSigTable).prefetched_entries & (1.U<<((addrToPrefetch>>6)(params.blk_bits-1,0)))) === 0.U){
                pref_out.bits.addr := addrToPrefetch
                pref_out.bits.write := io.snoop.bits.write
                pref_out.valid := true.B
                prefetch_active := true.B
                totalPrefetches := totalPrefetches + 1.U
                signature_table(indexSigTable).prefetched_entries := signature_table(indexSigTable).prefetched_entries | (1.U<<((addrToPrefetch>>6)(params.blk_bits-1,0)));
            } .otherwise {
               pref_out.valid := false.B
            }
            state := s_compute
        } .otherwise {
            state := s_lowconfidence
            when(crossPageBoundary){
                val ghrFreeSigMap = globalHistoryREG.map(_.sigEntry === 0.U)
                val ghrFreeSigIdx = PriorityEncoder(ghrFreeSigMap)
                val isghrFree = ghrFreeSigMap.reduce(_ || _)
                val lruList = globalHistoryREG.map(_.lru)
                val lruMin = lruList.reduce((a, b)=>Mux(a < b, a, b))
                val lruMinIdx = PriorityEncoder(lruList.map(_ === lruMin))
                val ghrAccessIdx = Mux(isghrFree, ghrFreeSigIdx, lruMinIdx)
                
                globalHistoryREG(ghrAccessIdx).sigEntry := currSig
                globalHistoryREG(ghrAccessIdx).sigConf := lookaheadConf
                globalHistoryREG(ghrAccessIdx).pageBoundaryLastOffset := currBlock_offset 
                globalHistoryREG(ghrAccessIdx).lastDelta := prefDelta
                globalHistoryREG(ghrAccessIdx).lru := 0.U
                state := s_idle
            }
        }
    } .elsewhen (state === s_lowconfidence){
        //In case of low confidence
    } .otherwise {
        state := s_idle
    }

    def callookaheadConfidence(throttle: UInt, prevC: UInt, currC: UInt): UInt = {
        val resConfidence = (throttle*prevC*currC) >> 18
        val finalRes = Mux((resConfidence > 255.U), 255.U(8.W), resConfidence(7,0))
        finalRes
    }

    def updatePht(sgTag: UInt, sgDelta: SInt): Unit = {
        val phtEntry = pht_table(sgTag)
        val hitVec = VecInit(phtEntry.delta_table.map(_.delta === sgDelta))
        val isHit  = hitVec.asUInt.orR
        val hitIdx = PriorityEncoder(hitVec)
        val minCDelta = phtEntry.delta_table.map(_.c_delta).reduce((a, b) => Mux(a < b, a, b))
        val replaceIdx = PriorityEncoder(phtEntry.delta_table.map(_.c_delta === minCDelta))

        pht_table(sgTag).c_sig := Mux(pht_table(sgTag).c_sig>=15.U, phtEntry.c_sig, phtEntry.c_sig + 1.U)

        when(isHit) {
            pht_table(sgTag).delta_table(hitIdx).c_delta := Mux(pht_table(sgTag).delta_table(hitIdx).c_delta>=15.U, phtEntry.delta_table(hitIdx).c_delta, phtEntry.delta_table(hitIdx).c_delta + 1.U)
        } .otherwise {
            pht_table(sgTag).delta_table(replaceIdx).delta   := sgDelta
            pht_table(sgTag).delta_table(replaceIdx).c_delta := 1.U
        }
    } 

    prefetch_queue.io.enq <> pref_out
    prefetch_queue.io.deq <> queue_out

    io.request.bits.address := prefetch_queue.io.deq.bits.addr
    io.request.valid := prefetch_active
    io.request.bits.write := prefetch_queue.io.deq.bits.write

    when (io.request.fire) {
        prefetch_queue.io.deq.ready := true.B
        reset_deq := true.B
        prefetch_active := false.B
    }

    when (reset_deq) {
        prefetch_queue.io.deq.ready := false.B
        reset_deq := false.B
    }
} 

class SignatureBuffer() extends Bundle {
  val patternSign = UInt(9.W)
  val signDelta   = SInt(7.W)
}

class SignatureTableEntries() extends Bundle {
  val pageTag     = UInt()
  val last_offset = UInt(6.W)
  val signature   = new SignatureBuffer()
  val prefetched_entries = UInt(64.W)
}

class PhtDeltaCon() extends Bundle{
    val delta = SInt(7.W)
    val c_delta = UInt(4.W)
}

class PatternHistoryTableEntries() extends Bundle{
    val sig_idx = UInt(9.W)
    val delta_table = Vec(4, new PhtDeltaCon())
    val c_sig = UInt(4.W)
}

class GlobalHistoryRegister() extends Bundle{
    val sigEntry = UInt(9.W)
    val sigConf = UInt(9.W)
    val pageBoundaryLastOffset = UInt(6.W)
    val lastDelta = SInt(7.W)
    val lru = UInt(8.W)
}

class prefetch_reqSPP() extends Bundle {
  val addr = UInt()
  val write = Bool()
}
