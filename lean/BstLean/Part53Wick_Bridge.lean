import BstLean.Part53Defs
import BstLean.Part41Contam
import BstLean.Part41Tensor
import BstLean.Part43Floor

namespace BstLean.Part53

set_option maxHeartbeats 1000000

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens IsSymmT contr trL glue)

variable {n d : ℕ}

private noncomputable def featureKernel53 (A : Tens n) (j : ℕ) (ψ : Mono n d → ℝ)
    (u : List (CoefIdxD n d)) : ℝ :=
  BstLean.Part41.Tl A j (u.map (fun α => α.2.2)) *
    (u.map (fun α => ψ (BstLean.Part41.pm α))).prod

private lemma featureKernel53_ofFn (A : Tens n) (j : ℕ) (ψ : Mono n d → ℝ)
    (α : Fin j → CoefIdxD n d) :
    featureKernel53 A j ψ (List.ofFn α) =
      A j (fun t => (α t).2.2) * ∏ t, ψ (BstLean.Part41.pm (α t)) := by
  simp only [featureKernel53, List.map_ofFn, BstLean.Part41.Tl_ofFn, List.prod_ofFn,
    Function.comp_def]

private lemma featureKernel53_symm (A : Tens n) (j : ℕ) (ψ : Mono n d → ℝ)
    (hA : IsSymmT (A j)) (u v : List (CoefIdxD n d)) (h : u.Perm v) :
    featureKernel53 A j ψ u = featureKernel53 A j ψ v := by
  unfold featureKernel53
  rw [BstLean.Part41.Tl_perm A j hA _ _ (h.map _), (h.map _).prod_eq]

private lemma feature_trace53 (A : Tens n) (m i : ℕ) (ψ : Mono n d → ℝ)
    (α : Fin m → CoefIdxD n d) :
    BstLean.Part41.traceL i (featureKernel53 A (m + 2 * i) ψ) (List.ofFn α) =
      nsq ψ ^ i * (∏ t, ψ (BstLean.Part41.pm (α t))) *
        trL i (A (m + 2 * i)) (fun t => (α ⟨t.1, by have := t.2; omega⟩).2.2) := by
  classical
  unfold BstLean.Part41.traceL featureKernel53 trL
  rw [BstLean.Part41.sum_split]
  simp only [List.map_append, BstLean.Part41.dblL_map, List.map_ofFn,
    List.prod_append, BstLean.Part41.dblL_prod, List.prod_ofFn, BstLean.Part41.Tl_glue]
  simp only [Function.comp_def]
  change ∑ p : Fin i → Mono n d, ∑ a : Fin i → Fin n,
      A (m + 2 * i) (glue (m + 2 * i) i a _) *
        ((∏ t, ψ (p t) ^ 2) * ∏ t, ψ (BstLean.Part41.pm (α t))) = _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hp : (∑ p : Fin i → Mono n d, ∏ t, ψ (p t) ^ 2) = nsq ψ ^ i := by
    rw [← Fintype.prod_sum (fun (_ : Fin i) (p : Mono n d) => ψ p ^ 2)]
    simp [nsq]
  rw [hp]
  ring

private lemma feature_inner53 (c : ℕ) (A A' : Tens n) (ψ ψ' : Mono n d → ℝ) :
    (∑ α : Fin c → CoefIdxD n d,
      featureKernel53 A c ψ (List.ofFn α) * featureKernel53 A' c ψ' (List.ofFn α)) =
      tinner (A c) (A' c) * (∑ p, ψ p * ψ' p) ^ c := by
  classical
  simp_rw [featureKernel53_ofFn]
  rw [BstLean.Part41.sum_split]
  change (∑ p : Fin c → Mono n d, ∑ a : Fin c → Fin n,
    (A c a * ∏ t, ψ (p t)) * (A' c a * ∏ t, ψ' (p t))) = _
  simp_rw [show ∀ p : Fin c → Mono n d, ∀ a : Fin c → Fin n,
    (A c a * ∏ t, ψ (p t)) * (A' c a * ∏ t, ψ' (p t)) =
      A c a * A' c a * ∏ t, ψ (p t) * ψ' (p t) by
        intro p a; rw [Finset.prod_mul_distrib]; ring]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (_ : Fin c) (p : Mono n d) => ψ p * ψ' p)]
  simp [tinner]

private lemma reindex_wick53 {R : Type*} [AddCommMonoid R] (k : ℕ) (g : ℕ → ℕ → R) :
    (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j / 2 + 1), g j i) =
      ∑ c ∈ Finset.range (k + 1),
        ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), g (c + 2 * i) i := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun p => ⟨p.1 - 2 * p.2, p.2⟩)
    (fun q => ⟨q.1 + 2 * q.2, q.2⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hp ⊢
    omega
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hq ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    apply Sigma.ext
    · dsimp
      omega
    · rfl
  · intro q hq
    ext <;> simp
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    simp only
    congr 1
    omega

private lemma heat_weight53 (v : ℝ) (c i : ℕ) :
    (v / 2) ^ i / (i.factorial : ℝ) *
      (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ)) =
        (BstLean.Part41.cQ (c + 2 * i) i : ℝ) * v ^ i := by
  simp only [BstLean.Part41.cQ, Nat.add_sub_cancel_right, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, div_pow]
  field_simp

private lemma heat_feature53 (k c : ℕ) (A : Tens n) (ψ : Mono n d → ℝ)
    (α : Fin c → CoefIdxD n d) :
    featureKernel53 (heatA k (nsq ψ) A) c ψ (List.ofFn α) =
      ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        (BstLean.Part41.cQ (c + 2 * i) i : ℝ) *
          BstLean.Part41.traceL i (featureKernel53 A (c + 2 * i) ψ) (List.ofFn α) := by
  classical
  simp only [featureKernel53_ofFn, heatA, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [heat_weight53, feature_trace53]
  ring

private lemma wick_heat53 (k c : ℕ) (A : Tens n) (ψ : Mono n d → ℝ) :
    BstLean.Part41.wickL c (featureKernel53 (heatA k (nsq ψ) A) c ψ) =
      ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        MvPolynomial.C (BstLean.Part41.cQ (c + 2 * i) i : ℝ) *
          BstLean.Part41.wickL c (BstLean.Part41.traceL i
            (featureKernel53 A (c + 2 * i) ψ)) := by
  classical
  unfold BstLean.Part41.wickL
  simp_rw [heat_feature53, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum, map_mul, mul_assoc]

private lemma polynomial_wick53 (k : ℕ) (A : Tens n) (ψ : Mono n d → ℝ)
    (hA : ∀ j, IsSymmT (A j)) :
    (∑ j ∈ Finset.range (k + 1), BstLean.Part41.plainL j (featureKernel53 A j ψ)) =
      ∑ c ∈ Finset.range (k + 1),
        BstLean.Part41.wickL c (featureKernel53 (heatA k (nsq ψ) A) c ψ) := by
  classical
  simp_rw [BstLean.Part41.plain_expand _ _ (featureKernel53_symm A _ ψ (hA _))]
  rw [reindex_wick53]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Nat.add_sub_cancel_right]
  exact (wick_heat53 k c A ψ).symm

private lemma tensor_cast_symm53 {a b : ℕ} (h : a = b)
    (A : (Fin a → Fin n) → ℝ) (hA : IsSymmT A) :
    IsSymmT (fun w : Fin b → Fin n => A (fun t => w ⟨t.1, by omega⟩)) := by
  subst b
  exact hA

private lemma heat_symm53 (k : ℕ) (v : ℝ) (A : Tens n)
    (hA : ∀ j, IsSymmT (A j)) (c : ℕ) : IsSymmT (heatA k v A c) := by
  classical
  intro σ w
  unfold heatA
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact tensor_cast_symm53 (by omega) _
    (BstLean.Part41.trL_symm i (by omega) _ (hA _)) σ w

private lemma feature_plain_eval53 (A : Tens n) (j : ℕ) (ψ : Mono n d → ℝ)
    (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval Z (BstLean.Part41.plainL j (featureKernel53 A j ψ)) =
      contr (A j) (fun _ => linZ Z ψ) := by
  classical
  rw [BstLean.Part41.eval_plainL]
  simp_rw [featureKernel53_ofFn]
  rw [BstLean.Part41.sum_split]
  unfold contr linZ
  simp_rw [Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro p hp
  change (A j a * ∏ t, ψ (p t)) * (∏ t, BstLean.Part41.colM Z (p t) (a t)) = _
  rw [Finset.prod_mul_distrib]
  ring

private lemma feature_fv_eval53 (k : ℕ) (A : Tens n) (ψ : Mono n d → ℝ)
    (hA : ∀ j, IsSymmT (A j)) (Z : CoefIdxD n d → ℝ) :
    fvA k A (linZ Z ψ) =
      MvPolynomial.eval Z (∑ c ∈ Finset.range (k + 1),
        BstLean.Part41.wickL c (featureKernel53 (heatA k (nsq ψ) A) c ψ)) := by
  rw [← polynomial_wick53 k A ψ hA]
  simp only [map_sum, feature_plain_eval53, fvA]

private lemma polynomial_integrable_wick53 {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e he
  have hprod (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) (e i))).const_mul _

-- These term elaborators reuse the proved private lemmas of Part 43. They only
-- resolve declaration names; the Lean kernel checks each resulting application.
elab "wickCrossImported53" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part43Floor.0.BstLean.Part43.wickL_cross")
    | throwError "Part43Floor.wickL_cross is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

elab "wickOrthogonalImported53" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part43Floor.0.BstLean.Part43.wickL_orthogonal")
    | throwError "Part43Floor.wickL_orthogonal is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

private lemma wick_cross53 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ) (H K : List ι → ℝ) (hK : ∀ u v, u.Perm v → K u = K v) :
    (∫ Z, MvPolynomial.eval Z (BstLean.Part41.wickL c H * BstLean.Part41.wickL c K)
      ∂stdGauss ι) = (c.factorial : ℝ) * ∑ w : Fin c → ι,
        H (List.ofFn w) * K (List.ofFn w) := by
  exact wickCrossImported53 c H K hK

private lemma wick_orthogonal53 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c r : ℕ) (H K : List ι → ℝ) (h : c ≠ r) :
    (∫ Z, MvPolynomial.eval Z (BstLean.Part41.wickL c H * BstLean.Part41.wickL r K)
      ∂stdGauss ι) = 0 := by
  exact wickOrthogonalImported53 c r H K h

private lemma wick_pair_sum53 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (H K : ℕ → List ι → ℝ) (hK : ∀ c u v, u.Perm v → K c u = K c v) :
    (∫ Z, MvPolynomial.eval Z
      ((∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H c)) *
       (∑ r ∈ Finset.range (k + 1), BstLean.Part41.wickL r (K r))) ∂stdGauss ι) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) *
        ∑ w : Fin c → ι, H c (List.ofFn w) * K c (List.ofFn w) := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  rw [integral_finsetSum _ (fun c hc => integrable_finsetSum _ (fun r hr =>
    polynomial_integrable_wick53 _))]
  apply Finset.sum_congr rfl
  intro c hc
  rw [integral_finsetSum _ (fun r hr => polynomial_integrable_wick53 _)]
  rw [Finset.sum_eq_single c]
  · simpa only [Finset.mul_sum] using wick_cross53 c (H c) (K c) (hK c)
  · intro r hr hrc
    exact wick_orthogonal53 r c (H r) (K c) hrc
  · exact fun h => (h hc).elim

private lemma wick_identity_unscaled53 (k : ℕ) (A A' : Tens n)
    (hA : ∀ j, IsSymmT (A j)) (hA' : ∀ j, IsSymmT (A' j))
    (ψ ψ' : Mono n d → ℝ) :
    (∫ Z, fvA k A (linZ Z ψ) * fvA k A' (linZ Z ψ') ∂stdGauss (CoefIdxD n d)) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) *
        tinner (heatA k (nsq ψ) A c) (heatA k (nsq ψ') A' c) *
          (∑ p, ψ p * ψ' p) ^ c := by
  classical
  let H := fun c => featureKernel53 (heatA k (nsq ψ) A) c ψ
  let K := fun c => featureKernel53 (heatA k (nsq ψ') A') c ψ'
  have hK : ∀ c u v, u.Perm v → K c u = K c v := by
    intro c u v huv
    exact featureKernel53_symm _ c ψ' (heat_symm53 k (nsq ψ') A' hA' c) u v huv
  calc
    _ = ∫ Z, MvPolynomial.eval Z
        ((∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H c)) *
         (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (K c)))
          ∂stdGauss (CoefIdxD n d) := by
      apply integral_congr_ae
      exact ae_of_all _ fun Z => by
        dsimp only [H, K]
        rw [map_mul, ← feature_fv_eval53 k A ψ hA Z,
          ← feature_fv_eval53 k A' ψ' hA' Z]
    _ = _ := by
      rw [wick_pair_sum53 k H K hK]
      apply Finset.sum_congr rfl
      intro c hc
      dsimp only [H, K]
      rw [feature_inner53]
      ring

private lemma linZ_scale53 (s : ℝ) (Z : CoefIdxD n d → ℝ) (ψ : Mono n d → ℝ) :
    linZ Z (s • ψ) = s • linZ Z ψ := by
  classical
  funext a
  simp only [linZ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private lemma nsq_scale53 (s : ℝ) (ψ : Mono n d → ℝ) : nsq (s • ψ) = s ^ 2 * nsq ψ := by
  classical
  simp [nsq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

private lemma inner_scale53 (s : ℝ) (ψ ψ' : Mono n d → ℝ) :
    (∑ p, (s • ψ) p * (s • ψ') p) = s ^ 2 * ∑ p, ψ p * ψ' p := by
  classical
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The Gaussian pair identity, with the frozen heat coefficients and scale. -/
theorem wick_identity53 (k : ℕ) (s : ℝ) (A A' : Tens n)
    (hA : ∀ j, IsSymmT (A j)) (hA' : ∀ j, IsSymmT (A' j))
    (ψ ψ' : Mono n d → ℝ) :
    (∫ Z, fvA k A (s • linZ Z ψ) * fvA k A' (s • linZ Z ψ')
      ∂stdGauss (CoefIdxD n d)) = wpair k s A A' ψ ψ' := by
  classical
  have h := wick_identity_unscaled53 k A A' hA hA' (s • ψ) (s • ψ')
  simp only [linZ_scale53, nsq_scale53, inner_scale53] at h
  rw [h]
  unfold wpair
  apply Finset.sum_congr rfl
  intro c hc
  rw [mul_pow, ← pow_mul]
  ring

end BstLean.Part53
