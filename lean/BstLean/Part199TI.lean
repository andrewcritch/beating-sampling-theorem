import BstLean.Part182TIA
import BstLean.Part182TImono
import BstLean.Part193Cover

/-! Part 199: variable-overlap TI certificates and mode separation.
The inherited TI estimate uses upper singular-value bounds.
Its charge is 51 exp(-tau) + 12 exp(-2 eta^2 mA), rather than the paper's sharper charge. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part182

/-- One checked scalar TI certificate. The overlap interval and all constants vary. -/
structure TICertificate (n : ℕ) where
  lo : ℝ
  hi : ℝ
  kE : ℝ
  ko : ℝ
  ks : ℝ
  eta : ℝ
  tau : ℝ
  lo_nonneg : 0 ≤ lo
  hi_lt_one : hi < 1
  kE_nonneg : 0 ≤ kE
  ko_nonneg : 0 ≤ ko
  ks_nonneg : 0 ≤ ks
  eta_nonneg : 0 ≤ eta
  tau_nonneg : 0 ≤ tau
  scalar_guards : ta_num n lo hi kE ko ks eta tau

noncomputable def TICertificate.lam {n : ℕ} (C : TICertificate n) : ℝ :=
  ta_lam C.kE C.ko C.ks

noncomputable def TICertificate.charge {n : ℕ} (C : TICertificate n) : ℝ :=
  51 * exp (-C.tau) + 12 * exp (-2 * C.eta ^ 2 * (mA n : ℕ))

theorem TICertificate.sound {n : ℕ} (hn : 2 ≤ n) (C : TICertificate n) :
    TI_hyp n C.lo C.hi C.lam C.charge :=
  ta_TI hn C.lo_nonneg C.hi_lt_one C.eta_nonneg C.tau_nonneg
    C.kE_nonneg C.ko_nonneg C.ks_nonneg C.scalar_guards

/-- A deterministic overlap cover selects one fixed-pair proof before the weights are drawn.
There is no union of weight events over the cells. -/
theorem TI_of_cover {n : ℕ} (hn : 2 ≤ n) {lo hi lam δ : ℝ} {ι : Type*}
    (cover : BstLean.Part193.FiniteCover ℝ ι (Set.Icc lo hi))
    (cert : ι → TICertificate n)
    (contains : ∀ i ∈ cover.indices, ∀ c ∈ Set.Icc lo hi, c ∈ cover.cell i →
      (cert i).lo ≤ c ∧ c ≤ (cert i).hi)
    (hlam : ∀ i ∈ cover.indices, (cert i).lam ≤ lam)
    (hcharge : ∀ i ∈ cover.indices, (cert i).charge ≤ δ) :
    TI_hyp n lo hi lam δ := by
  intro x x' hx hx' hlo hhi
  obtain ⟨i, hi, hcell⟩ := cover.covers (x ⬝ᵥ x') ⟨hlo, hhi⟩
  obtain ⟨hl, hu⟩ := contains i hi _ ⟨hlo, hhi⟩ hcell
  have hlocal := TI_hyp_mono (hlam i hi) (hcharge i hi) ((cert i).sound hn)
  exact hlocal x x' hx hx' hl hu

/-- Two independently proved integrated scalar bounds permit their minimum.
This lemma does not assert a pointwise tangential gain. -/
theorem integrated_min {Q K L : ℝ} (hK : Q ≤ K) (hL : Q ≤ L) : Q ≤ min K L :=
  le_min hK hL

theorem mode_separation {n m : ℕ} {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) (hc : (x ⬝ᵥ x') ^ 2 < 1)
    (J J' : Matrix (Fin m) (Fin n) ℝ) {kE ko ks : ℝ}
    (hE0 : 0 ≤ kE) (ho0 : 0 ≤ ko) (hs0 : 0 ≤ ks)
    (hE : opN (PEm x x' * (Jᵀ * J') * PEm x x') ≤ (n : ℝ) * kE)
    (ho1 : BstLean.Part153.nrm (PEm x x' *ᵥ ((Jᵀ * J') *ᵥ eTan x' x)) ≤ (n : ℝ) * ko)
    (ho2 : BstLean.Part153.nrm (PEm x x' *ᵥ ((J'ᵀ * J) *ᵥ eTan x x')) ≤ (n : ℝ) * ko)
    (hs : |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ (n : ℝ) * ks) :
    opN ((J * BstLean.Part153.projT x)ᵀ * (J' * BstLean.Part153.projT x')) ≤
      (n : ℝ) * ta_lam kE ko ks := by
  have h := ms_opN hx hx' hc J J'
    (mul_nonneg (Nat.cast_nonneg n) hE0) (mul_nonneg (Nat.cast_nonneg n) ho0)
    (mul_nonneg (Nat.cast_nonneg n) hs0) hE ho1 ho2 hs
  rwa [ta_lam_scale (Nat.cast_nonneg n)] at h

end BstLean.Part199
