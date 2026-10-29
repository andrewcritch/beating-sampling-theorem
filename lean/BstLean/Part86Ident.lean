import BstLean.Part86Defs
import BstLean.Part56Weights
import BstLean.Part56Orth_Heat
import BstLean.Part56MomProg_Basic
import BstLean.Part53Laws
import BstLean.Part49Main

/-!
# Part 86, identification of the sphere quantities with the model quantities (`Ident86`)

`ident86`: for `Z` with `(U, W) = (Uof v Z, Wof E Z)`, `W ≠ 0`: `BofQ`, `varFQ` at `unitOfD Z` under
`lawRK` are `Bm`, `Vm` of the model `modRK` for the polynomial `PU … U r σ` at the scale `λ₀` and
the point `√D_W · W/‖W‖`; the weight form of the line program at the surrogate is `gqRK`.
-/

namespace BstLean.Part86.XIdent

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD monoVal)
open BstLean.Part41 (Mono phiM colM varU frob IsSymmT Tens TSymm fval contr)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (heatA tinner fvA unitF53 radF53 linZ nsq TF sg)
open BstLean.Part56 (UnitV lawRK surrRK KRK phiB kJ KR tauR ancRK gLineW gLineH mux betaJ
  axialMeasure polarState polarPoint perpDir axialR axialS)
open BstLean.Part78 (zv)

/-! ## The polynomial of `f` -/

section alg

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

lemma eval_fPoly (k : ℕ) (f0 : ℝ) (T : Tens n) (y : Fin n → ℝ) :
    MvPolynomial.eval y (fPoly k f0 T) = fval k f0 T y := by
  unfold fPoly fval contr
  simp only [map_add, MvPolynomial.eval_C, map_sum, map_mul, map_prod, MvPolynomial.eval_X]

lemma eval_PU (k : ℕ) (f0 : ℝ) (T : Tens n) (U : I × Fin n → ℝ) (r sc : ℝ)
    (w : I ⊕ Fin n → ℝ) :
    MvPolynomial.eval w (PU k f0 T U r sc) =
      fval k f0 T (fun i => ∑ j : I, U (j, i) / r * w (Sum.inl j) + sc * w (Sum.inr i)) := by
  unfold PU
  rw [show (MvPolynomial.eval w) = MvPolynomial.eval₂Hom (RingHom.id ℝ) w from rfl,
    MvPolynomial.eval₂Hom_bind₁, ← eval_fPoly]
  show MvPolynomial.eval _ _ = _
  congr 2
  funext i
  simp only [map_add, map_sum, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X, RingHom.id_apply]

lemma Fm_PU (M : Mod n I J S G) (k : ℕ) (f0 : ℝ) (T : Tens n) (U : I × Fin n → ℝ) (r sc lam : ℝ)
    (W : J × Fin n → ℝ) (x : Fin n → ℝ) :
    Fm M (PU k f0 T U r sc) lam W x =
      fval k f0 T (fun i => ∑ j : I, U (j, i) / r * M.b x j + sc * (lam * zv W (M.ps x) i)) := by
  unfold Fm
  rw [eval_PU]
  rfl

lemma continuous_fval (k : ℕ) (f0 : ℝ) (T : Tens n) : Continuous (fval k f0 T) := by
  unfold fval contr
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro w _
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro t _
  exact continuous_apply _

lemma zv_smul' (a : ℝ) (W : J × Fin n → ℝ) (p : J → ℝ) (i : Fin n) :
    zv (a • W) p i = a * zv W p i := by
  simp only [zv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

end alg

/-! ## Linearity of the coordinates -/

section coords

variable {n d : ℕ}

lemma Uof_smul (v : Fin n → ℝ) (s : ℝ) (Z : CoefIdxD n d → ℝ) (a : Fin (d + 1) × Fin n) :
    Uof v (s • Z) a = s * Uof v Z a := by
  unfold Uof
  rw [BstLean.Part56.Orth.anchor_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma Wof_smul (E : JR n d → Mono n d → ℝ) (s : ℝ) (Z : CoefIdxD n d → ℝ) :
    Wof E (s • Z) = s • Wof E Z := by
  funext a
  simp only [Wof, colM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

lemma eval_monoP (x : Fin n → ℝ) (p : Mono n d) : MvPolynomial.eval x (monoP p) = phiM x p := by
  unfold monoP phiM monoVal
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp

lemma eval_bPE (v x : Fin n → ℝ) (j : Fin (d + 1)) :
    MvPolynomial.eval x (bPE d v j) = kJ d j x v / Real.sqrt (kJ d j v v) := by
  unfold bPE kJ
  simp only [map_sum, map_mul, MvPolynomial.eval_C, eval_monoP]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  unfold phiB
  split_ifs <;> ring

lemma zv_Wof (E : JR n d → Mono n d → ℝ) (Z : CoefIdxD n d → ℝ) (ψ : JR n d → ℝ) (s : ℝ) :
    (fun i => s * zv (Wof E Z) ψ i) = linZ Z (fun p => s * ∑ q, E q p * ψ q) := by
  funext i
  simp only [zv, Wof, linZ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma nsq_Et (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) (ψ : JR n d → ℝ)
    (s : ℝ) : nsq (fun p : Mono n d => s * ∑ q, E q p * ψ q) = s ^ 2 * ∑ q, ψ q ^ 2 := by
  unfold nsq
  have h1 : ∀ p : Mono n d, (s * ∑ q, E q p * ψ q) ^ 2 =
      s ^ 2 * ∑ q, ∑ q', ψ q * ψ q' * (E q p * E q' p) := by
    intro p
    rw [mul_pow, pow_two (∑ q, E q p * ψ q), Finset.sum_mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro q' _
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hE.1]
  simp [pow_two]

end coords

/-! ## Integrals over `lawRK` as slice integrals -/

section law

variable {m : ℕ}

lemma lawRK_integral_slices (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (h : (Fin (m + 1) → ℝ) → ℝ) (hc : Continuous h) :
    ∫ x, h x ∂lawRK (m + 1) t v =
      ∫ p, ∫ g, h (polarState v (p, g)) ∂stdGauss (Fin (m + 1)) ∂axialMeasure t v := by
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb' : b 0 = WithLp.toLp 2 v := hb
  have hsph : BstLean.Part40.SphLaw (m + 1) (lawRK (m + 1) t v) :=
    (BstLean.Part50.binghamA_antipodal (by omega) (BstLean.Part56.rk1 t v)).sph
  have hint : Integrable h (lawRK (m + 1) t v) := BstLean.Part56.integrable_cont_sph56 hsph hc
  have hmap := BstLean.Part56.lawRK_eq_polar_map b v hb' t
  have hpm := BstLean.Part56.measurable_polarState v
  have := BstLean.Part56.axialMeasure_probability b v hb' t
  rw [hmap] at hint ⊢
  rw [integral_map hpm.aemeasurable hc.aestronglyMeasurable]
  have hint' := (integrable_map_measure hc.aestronglyMeasurable hpm.aemeasurable).mp hint
  exact integral_prod _ hint'

end law

/-! ## The identification -/

section main

variable {m d : ℕ}

lemma gauss_W_transfer (v : Fin (m + 1) → ℝ) (E : JR (m + 1) d → Mono (m + 1) d → ℝ)
    (hmp : MeasurePreserving (fun Z : CoefIdxD (m + 1) d → ℝ => (Uof v Z, Wof E Z))
      (stdGauss (CoefIdxD (m + 1) d))
      ((stdGauss (Fin (d + 1) × Fin (m + 1))).prod (stdGauss (JR (m + 1) d × Fin (m + 1)))))
    (G : (JR (m + 1) d × Fin (m + 1) → ℝ) → ℝ) (hG : Continuous G) :
    ∫ W, G W ∂stdGauss (JR (m + 1) d × Fin (m + 1)) =
      ∫ Z, G (Wof E Z) ∂stdGauss (CoefIdxD (m + 1) d) := by
  have h1 : (stdGauss (CoefIdxD (m + 1) d)).map (fun Z => Wof E Z) =
      stdGauss (JR (m + 1) d × Fin (m + 1)) := by
    have h2 : (fun Z : CoefIdxD (m + 1) d → ℝ => Wof E Z) =
        Prod.snd ∘ (fun Z : CoefIdxD (m + 1) d → ℝ => (Uof v Z, Wof E Z)) := rfl
    rw [h2, ← Measure.map_map measurable_snd hmp.measurable, hmp.map_eq, Measure.map_snd_prod]
    simp
  have hmeas : Measurable (fun Z : CoefIdxD (m + 1) d → ℝ => Wof E Z) := hmp.measurable.snd
  rw [← h1, integral_map hmeas.aemeasurable hG.aestronglyMeasurable]

theorem ident86 (m d k K : ℕ) (hd : 1 ≤ d) (hRF : RotFacts (m + 1) d) : Ident86 m d k K := by
  intro t v ht hv E hE f0 T hT Z hW
  obtain ⟨hmp, hsq, hmap, hKR, -, -⟩ := hRF v hv E hE
  set M := modRK m d t v E with hM
  set U := Uof v Z with hU
  set W := Wof E Z with hWd
  set ρ := radF53 W with hρd
  set r := Real.sqrt (∑ a, U a ^ 2 + ρ ^ 2) with hrd
  set σ := 1 / Real.sqrt (DD (m + 1) d) with hσ
  set DW := DWr (m + 1) (JR (m + 1) d) with hDWd
  set lam := lam0 (DD (m + 1) d) DW U ρ with hlam
  set P := PU k f0 T U r σ with hP
  -- positivity facts
  have hWsq : 0 < ∑ a, W a ^ 2 := by
    by_contra hcon
    apply hW
    have hz : ∑ a, W a ^ 2 = 0 :=
      le_antisymm (not_lt.mp hcon) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (W a))).mp hz a
      (Finset.mem_univ a)
    simpa using this
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hWsq
  have hρ2 : ρ ^ 2 = ∑ a, W a ^ 2 := Real.sq_sqrt hWsq.le
  have hr : r = Real.sqrt (∑ α, Z α ^ 2) := by
    rw [hrd, hρ2, hsq Z]
  have hUsq : 0 ≤ ∑ a, U a ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by rw [hρ2]; linarith)
  have hDWpos : 0 < DW := by
    rw [hDWd]; unfold DWr
    have hne : Nonempty (JR (m + 1) d × Fin (m + 1)) := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      apply hW
      funext a
      exact hcon.elim a
    exact_mod_cast Fintype.card_pos
  have hDDpos : 0 < DD (m + 1) d := by
    unfold DD
    have : Nonempty (CoefIdxD (m + 1) d) := ⟨⟨0, (Sym.nil, 0)⟩⟩
    exact_mod_cast Fintype.card_pos
  have hsD : 0 < Real.sqrt (DD (m + 1) d) := Real.sqrt_pos.mpr hDDpos
  have hsW : 0 < Real.sqrt DW := Real.sqrt_pos.mpr hDWpos
  have hunit : unitOfD Z = (1 / r) • Z := by
    unfold unitOfD; rw [hr]
  -- (A) the pointwise identity
  have hA : ∀ x, Fm M P lam (Real.sqrt DW • unitF53 W) x =
      fval k f0 T (mapMD (unitOfD Z) x) := by
    intro x
    rw [hP, Fm_PU]
    congr 1
    funext i
    rw [hmap (unitOfD Z) x i, hunit, Wof_smul, zv_smul', zv_smul']
    simp_rw [Uof_smul]
    have hu : unitF53 W = (1 / ρ) • W := rfl
    rw [hu, zv_smul']
    have hb : ∀ j, M.b x j = MvPolynomial.eval x (bPE d v j) := fun j => rfl
    have hps : M.ps x = fun q => MvPolynomial.eval x (psPE E q) := rfl
    simp_rw [hb, hps]
    have hscal : σ * (lam * (Real.sqrt DW * (1 / ρ))) = 1 / r := by
      rw [hσ, hlam]; unfold lam0
      rw [← hrd]
      field_simp
    have e1 : σ * (lam * (Real.sqrt DW * (1 / ρ *
        zv W (fun q => MvPolynomial.eval x (psPE E q)) i))) =
        1 / r * zv W (fun q => MvPolynomial.eval x (psPE E q)) i := by
      rw [← hscal]; ring
    rw [e1]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- (B)
  have hcont : Continuous (fun x => fval k f0 T (mapMD (unitOfD Z) x)) :=
    (continuous_fval k f0 T).comp
      (continuous_pi fun a => BstLean.Part49.continuous_mapMD (unitOfD Z) a)
  have hB : BofQ (lawRK (m + 1) t v) k f0 T (unitOfD Z) =
      Bm M P lam (Real.sqrt DW • unitF53 W) := by
    unfold BofQ Bm msl Fs
    rw [lawRK_integral_slices t v hv _ hcont]
    simp_rw [hA]
    rfl
  refine ⟨hB, ?_, ?_⟩
  · unfold varFQ varU Vm Fs
    rw [← hB]
    have hc2 : Continuous (fun x => (fval k f0 T (mapMD (unitOfD Z) x) -
        BofQ (lawRK (m + 1) t v) k f0 T (unitOfD Z)) ^ 2) :=
      (hcont.sub continuous_const).pow 2
    have := lawRK_integral_slices t v hv _ hc2
    unfold BofQ at this ⊢
    rw [this]
    simp_rw [hA]
    rfl
  · have hQ : BstLean.Part40.SphLaw (m + 1) (surrRK (m + 1) K t v) :=
      BstLean.Part56.MomProg.surrRK_sphLaw (by omega) K t ht v
    rw [BstLean.Part56.propWeights56 d k (m + 1) _ hQ v hv f0 T hT (unitOfD Z)]
    unfold gLineH gqRK
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x => ?_
    show _ = Phi M P 1 x
    unfold Phi
    set ψ : JR (m + 1) d → ℝ := fun q => MvPolynomial.eval x (psPE E q) with hψ
    set y : Fin (m + 1) → ℝ := fun i => ∑ j : Fin (d + 1), U (j, i) / r * M.b x j with hy
    have hF : ∀ W' : JR (m + 1) d × Fin (m + 1) → ℝ,
        Fm M P 1 W' x = fvA k (TF k f0 T) (y + fun i => σ * zv W' ψ i) := by
      intro W'
      rw [hP, Fm_PU, BstLean.Part53.fvA_TF]
      congr 1
      funext i
      simp only [Pi.add_apply, hy, one_mul]
      rfl
    simp_rw [hF]
    have hGc : Continuous (fun W' : JR (m + 1) d × Fin (m + 1) → ℝ =>
        fvA k (TF k f0 T) (y + fun i => σ * zv W' ψ i)) := by
      simp_rw [BstLean.Part53.fvA_TF]
      apply (continuous_fval k f0 T).comp
      apply continuous_pi
      intro i
      simp only [Pi.add_apply, zv]
      fun_prop
    rw [gauss_W_transfer v E hmp _ hGc]
    simp_rw [zv_Wof]
    rw [BstLean.Part56.Orth.linear_heat_mean k (TF k f0 T)
      (fun j => BstLean.Part53.TF_symm k f0 T hT j), nsq_Et v E hE]
    have hτ : ∑ q, ψ q ^ 2 = tauR d v x := by
      have := hKR x x
      unfold tauR
      rw [← this]
      exact Finset.sum_congr rfl fun q _ => by rw [pow_two]
    have hsg : sg (m + 1) d = σ := rfl
    rw [hτ, hsg]
    congr 1
    -- the mean field
    funext i
    unfold mux
    rw [hunit]
    simp only [hy, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      BstLean.Part56.Orth.anchor_smul]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => betaJ d j v x * (1 / r * ancRK Z v j i)) (d + 1)]
    apply Finset.sum_congr rfl
    intro j _
    have hb : M.b x j = MvPolynomial.eval x (bPE d v j) := rfl
    have hk : 0 < kJ d (j : ℕ) v v :=
      BstLean.Part56.Orth.block_norm_pos v hv j (by have := j.2; omega)
    have hs : Real.sqrt (kJ d (j : ℕ) v v) * Real.sqrt (kJ d (j : ℕ) v v) = kJ d (j : ℕ) v v :=
      Real.mul_self_sqrt hk.le
    have hs0 : 0 < Real.sqrt (kJ d (j : ℕ) v v) := Real.sqrt_pos.mpr hk
    rw [hb, eval_bPE, hU]
    unfold Uof betaJ
    simp only
    field_simp
    rw [Real.sq_sqrt hk.le]
    ring

end main

end BstLean.Part86.XIdent

#print axioms BstLean.Part86.XIdent.ident86
