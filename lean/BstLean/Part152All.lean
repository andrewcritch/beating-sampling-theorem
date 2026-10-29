import BstLean.Part152GC
import BstLean.Part152LM
import BstLean.Part152OpMom

/-!
# Part 152 (file `All`): the audit of the headline statements

Role: `delegations/statements/p152-spec.md`. Every name below must give
`[propext, Classical.choice, Quot.sound]` and nothing else.
-/

open BstLean.Part152

-- file `BM`
#print axioms bm_add
#print axioms bm_convex
#print axioms pl_one
-- file `Tau`
#print axioms tau_gauss1
#print axioms Tau.prod
#print axioms Tau.map
#print axioms tau_stdGauss
-- file `GC`
#print axioms gaussConc_mgf_sharp
#print axioms gaussConc_lower_sharp
#print axioms gaussConc_upper_sharp
#print axioms gaussVar_le_sharp
#print axioms gaussConc_mat_lower_sharp
#print axioms gaussConc_mat_upper_sharp
#print axioms gaussVar_mat_le_sharp
-- file `LM` (written by a helper agent; statements read and audited here)
#print axioms chiSq_upper_LM
#print axioms chiSq_lower_LM
#print axioms gaussConc_moment
-- file `SF`
#print axioms stein1
#print axioms stein_coord
#print axioms sudakovFernique
-- file `Op`
#print axioms mulVec_le_opN
#print axioms opN_le_frob
#print axioms opN_lip
#print axioms opN_mean_le
#print axioms opN_tail
#print axioms opN_tail'
-- file `OpMom`
#print axioms gaussConc_mat_moment
#print axioms moment_shift
#print axioms opN_moment
