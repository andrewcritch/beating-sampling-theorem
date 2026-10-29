import BstLean.Part56MomProg_VecProg
import BstLean.Part56MomProg_CostDefs

/-! The stage values of the moment program. -/

namespace BstLean.Part56.MomProg

open BstLean.Part56
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

section values
variable (d D : ℕ)

noncomputable def RmF (a : Fin n) (v : Fin n → ℝ) : Fin n × Fin n → ℝ :=
  fun ml => Rmat a v ml.1 ml.2

noncomputable def pvF (v : Fin n → ℝ) : Mono n d → ℝ := fun p => phiM v p

noncomputable def kiF (v : Fin n → ℝ) : Fin (d + 1) → ℝ := fun j => 1 / kJ d j v v

noncomputable def imgF (R : Fin n × Fin n → ℝ) : Mono n d × Idx n D → ℝ := fun pμ =>
  plist ((pμ.1.2.val.toList).map fun m => linVec (fun j => R (m, j))) pμ.2

noncomputable def kerF (pv : Mono n d → ℝ) (img : Mono n d × Idx n D → ℝ) :
    Fin (d + 1) × Idx n D → ℝ := fun jμ =>
  ∑ p : Mono n d, (if (p.1 : ℕ) = (jμ.1 : ℕ) then pv p else 0) * img (p, jμ.2)

noncomputable def sqF (img : Mono n d × Idx n D → ℝ) : Mono n d × Idx n D → ℝ := fun pμ =>
  pmul (fun μ => img (pμ.1, μ)) (fun μ => img (pμ.1, μ)) pμ.2

noncomputable def kkF (ker : Fin (d + 1) × Idx n D → ℝ) : Fin (d + 1) × Idx n D → ℝ := fun jμ =>
  pmul (fun μ => ker (jμ.1, μ)) (fun μ => ker (jμ.1, μ)) jμ.2

noncomputable def diagF (sq : Mono n d × Idx n D → ℝ) : Fin (d + 1) × Idx n D → ℝ := fun jμ =>
  ∑ p : Mono n d, (if (p.1 : ℕ) = (jμ.1 : ℕ) then sq (p, jμ.2) else 0) * 1

noncomputable def tauF (diag : Fin (d + 1) × Idx n D → ℝ) (ki : Fin (d + 1) → ℝ)
    (kk : Fin (d + 1) × Idx n D → ℝ) : Idx n D → ℝ := fun μ =>
  ∑ j : Fin (d + 1), if 1 ≤ (j : ℕ) then diag (j, μ) - ki j * kk (j, μ) else 0

noncomputable def betaF (ki : Fin (d + 1) → ℝ) (ker : Fin (d + 1) × Idx n D → ℝ) :
    Fin (d + 1) × Idx n D → ℝ := fun jμ => ki jμ.1 * ker jμ

/-- The list of factors of a key: `l` copies of `τ`, then `β_{j_r}`. -/
def keyList {k : ℕ} (κ : KeyRK k d) : List (Option (Fin (d + 1))) :=
  List.replicate (κ.1.2 : ℕ) none ++ List.ofFn (fun r => some (κ.2 r))

noncomputable def QF {k : ℕ} (tb : Option (Fin (d + 1)) × Idx n D → ℝ) :
    KeyRK k d × Idx n D → ℝ := fun κμ =>
  plist ((keyList d κμ.1).map fun o μ => tb (o, μ)) κμ.2

noncomputable def TF (a : Fin n) (K : ℕ) (t : ℝ) : Idx n D → ℝ := fun μ => Ttab a K t μ.1

noncomputable def WF {k : ℕ} (Q : KeyRK k d × Idx n D → ℝ) (T : Idx n D → ℝ) : KeyRK k d → ℝ :=
  fun κ => wickC κ.1.1 κ.1.2 * (1 / BstLean.Part36.DD n d) ^ (κ.1.2 : ℕ) *
    ((∑ μ : Idx n D, Q (κ, μ) * T μ) / T (Idx.zero D))

/-- The `τ`/`β` table. -/
noncomputable def tbF (diag : Fin (d + 1) × Idx n D → ℝ) (ki : Fin (d + 1) → ℝ)
    (kk ker : Fin (d + 1) × Idx n D → ℝ) : Option (Fin (d + 1)) × Idx n D → ℝ := fun oμ =>
  match oμ.1 with
  | none => tauF d D diag ki kk oμ.2
  | some j => betaF d D ki ker (j, oμ.2)

/-- The whole value, from `t` and `v`. -/
noncomputable def fullF (a : Fin n) (K k : ℕ) (t : ℝ) (v : Fin n → ℝ) : KeyRK k d → ℝ :=
  let img := imgF d D (RmF a v)
  let ker := kerF d D (pvF d v) img
  WF d D (QF d D (tbF d D (diagF d D (sqF d D img)) (kiF d v) (kkF d D ker) ker)) (TF D a K t)

end values

end BstLean.Part56.MomProg
