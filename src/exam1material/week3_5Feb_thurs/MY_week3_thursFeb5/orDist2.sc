// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orDist2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( (p | q ) & (p | r) ) |- ( p | (q & r) )
      Proof(
        //PROOF GOES HERE
        1( (p | q) & (p | r) ) by Premise,
        2 ( p | q ) by AndE1(1),
        3 (p | r) by AndE2(1),
        4 SubProof(
          5 Assume(p)
          6 ( p | ( q & r) ) by OrI1(5)
        )
        //Assume q
        7 SubProof(
          8 Assume(q),

          //OrE subproofs with ( p | r)
          // Assume p, assume r
          9 SubProof(
            10 Assume (p),
            11 ( p | ( q & r) ) by OrI1(10)
            
          )
          12 SubProof(
            13 Assume(r)
            14 
          )

        )

        
    )
  )
}