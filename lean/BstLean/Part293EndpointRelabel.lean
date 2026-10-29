import BstLean.Part293EndpointInterface

/-! Rewriting exact rational cell boundaries preserves the END payment. -/
namespace BstLean.Part293
open BstLean.Part232

noncomputable def relabelEnd {n c c' f a h H H' : ℝ}
    (hc : c' = c) (hH : H' = H) (e : EndCertificate n c f a h H) :
    EndCertificate n c' f a h H' := by
  rw [hc, hH]
  exact e

@[simp] theorem relabelEnd_payment {n c c' f a h H H' : ℝ}
    (hc : c' = c) (hH : H' = H) (e : EndCertificate n c f a h H) :
    (relabelEnd hc hH e).payment = e.payment := by
  subst c'
  subst H'
  rfl

end BstLean.Part293
