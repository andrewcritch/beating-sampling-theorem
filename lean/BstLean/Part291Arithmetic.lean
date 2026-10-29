import BstLean.Part291Band
import BstLean.Part291Weighted

/-! The final WF arithmetic is separate from the enclosures of its analytic inputs. -/
namespace BstLean.BlueprintLow
open Real Set MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157

structure FrameScalarData where
  projected : ℝ
  cap : ℝ
  mean1 : ℝ
  mean2 : ℝ
  mass : ℝ
  projectedRoot : ℝ
  capRoot : ℝ
  mean1Root : ℝ
  mean2Root : ℝ

structure FrameScalarCertificate (r : FrameScalarData) : Prop where
  roots_nonneg : 0 ≤ r.projectedRoot ∧ 0 ≤ r.capRoot ∧
    0 ≤ r.mean1Root ∧ 0 ≤ r.mean2Root
  roots : r.projected ≤ r.projectedRoot ^ 2 ∧ r.cap ≤ r.capRoot ^ 2 ∧
    r.mean1 ≤ r.mean1Root ^ 2 ∧ r.mean2 ≤ r.mean2Root ^ 2
  total : (r.projectedRoot + r.capRoot) ^ 2 +
    (r.mean1Root + r.mean2Root) ^ 2 + r.mass < weightedFrameCap

theorem frame_scalar_bound {r : FrameScalarData} (C : FrameScalarCertificate r)
    {N B U V mass : ℝ} (hN : N ≤ r.projected) (hB : B ≤ r.cap)
    (hU : U ≤ r.mean1) (hV : V ≤ r.mean2) (hm : mass ≤ r.mass) :
    (√N + √B) ^ 2 + (√U + √V) ^ 2 + mass < weightedFrameCap := by
  have h1 : √N ≤ r.projectedRoot := sqrt_le_iff.mpr ⟨C.roots_nonneg.1, hN.trans C.roots.1⟩
  have h2 : √B ≤ r.capRoot := sqrt_le_iff.mpr ⟨C.roots_nonneg.2.1, hB.trans C.roots.2.1⟩
  have h3 : √U ≤ r.mean1Root := sqrt_le_iff.mpr ⟨C.roots_nonneg.2.2.1, hU.trans C.roots.2.2.1⟩
  have h4 : √V ≤ r.mean2Root := sqrt_le_iff.mpr ⟨C.roots_nonneg.2.2.2, hV.trans C.roots.2.2.2⟩
  apply lt_of_le_of_lt _ C.total
  gcongr

/-- Application of a checked scalar certificate to an actual network unit test.
Each enclosure hypothesis names an analytic quantity; none is inferred from Python. -/
theorem weighted_unit_test_of_certificate {n : ℕ} (hn : 6 ≤ n)
    (D : Design n) (c : Ret n) (v : Fin (mA n) → ℝ) (hv : normSq v = 1)
    {a d N C xi Ncov Vpsi W Beta : ℝ}
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hd : 0 < d) (hN : 0 ≤ N) (hC : 0 ≤ C) (hNc : 0 ≤ Ncov)
    (hV : 0 ≤ Vpsi) (hW : 0 ≤ W)
    (S : WeightedTestBounds D c v a d N C xi Ncov Vpsi W Beta)
    {r : FrameScalarData} (R : FrameScalarCertificate r)
    (eN : N ≤ r.projected) (eC : C ≤ r.cap)
    (eU : W ^ 2 * xi ≤ r.mean1) (eV : Vpsi * Ncov ≤ r.mean2) (eB : Beta ≤ r.mass) :
    (n : ℝ) * ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * v j) ^ 2
      ∂stdGauss (Fin n) < weightedFrameCap := by
  have h := weighted_unit_test hn D c v hv hτ hb hd hN hC hNc hV hW S
  have he : √(W ^ 2 * xi) = W * √xi := by rw [sqrt_mul (sq_nonneg _), sqrt_sq hW]
  exact h.trans_lt (by simpa only [he] using frame_scalar_bound R eN eC eU eV eB)

end BstLean.BlueprintLow
