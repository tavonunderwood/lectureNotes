// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


@pure def orDist1(p: B, q: B, r: B): Unit = {
  Deduce(
    (p | (q & r)) |- ( (p | q ) & (p | r) )
      Proof(
        //PROOF GOES HERE
        1 ( p | (q & r) ) by Premise,
        // Use orE ont he premise
        2 SubProof(
          3 Assume(p)
          4 ( p | q ) by OrI1(3)
          5 ( p | r ) by OrI1(3)
          6 ( p | q ) & (p | r) by AndI(4, 50)
          
        )
        7 SubProof(
          8 Assume(q & r)
          9 ( q ) by AndE1(8)
          10 ( r ) by AndE2(9)
          11 ( p | q ) by OrI2(9)
          12 (p | r) by OrI2(10)
        )
        //goal:(p | q ) & (p | r)
        
    )
  )
}