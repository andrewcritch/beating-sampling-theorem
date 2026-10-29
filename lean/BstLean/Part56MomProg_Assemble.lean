import BstLean.Part56MomProg_StageE
import BstLean.Part56MomProg_StageF
import BstLean.Part56MomProg_ValueEq

/-! The whole moment program. -/

namespace BstLean.Part56.MomProg

open BstLean.Cost BstLean.Part56
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

lemma hp_full (hn : 1 ≤ n) (a : Fin n) (d k K : ℕ) :
    HasProg (fun (w : InM56 n → ℝ) =>
      fullF d (2 * d * k) a K k (w (Sum.inl ())) (fun l => w (Sum.inr l)))
      (costAll n d k K (Fintype.card (Idx n (2 * d * k))) (Fintype.card (Mono n d))
        (Fintype.card (KeyRK k d))) := by
  have hA := hp_stageA a d
  have hB := hp_stageB (n := n) d (2 * d * k)
  have hTB := hp_seq (hp_seq hA (hp_keep hB)) (hp_stageC (n := n) d (2 * d * k))
  have hQ := hp_seq hTB (hp_stageD (n := n) d (2 * d * k) k)
  have hT := hp_mapIn (hp_stageE hn a d k K) (fun _ : Unit => (Sum.inl () : InM56 n))
  have hF := hp_seq (hp_pair hQ hT) (hp_stageF (n := n) d (2 * d * k) k)
  refine hp_mono (hp_congr hF (fun w κ => rfl)) ?_
  unfold costAll
  omega

end BstLean.Part56.MomProg
