import BstLean.Part72Good

/-!
# Part 72: the main-term tensors from overlap moments (every `d`, every `c`)

Source: `delegations/answers/omOV-opus-prover.md` §2.2 (Lemma O1 and Proposition M). The route
here avoids Newton's identities.

For a distribution `μ` carried by the sphere, write `u = x·y` for two independent draws
(`μ ⊗ μ`), `Mean μ = Σ_i (E_μ x_i)² = E u` and `Ov2 μ = E u²`.

* `featDev_le_overlap`: `featDev d μ c ≤ E_{μ⊗μ} S(u)^c − 1`, `S(u) = Σ_{j ≤ d} u^j`.
  Proof: index the monomials by words (`symOf`, a surjection), then
  `Σ_W (E_μ G_W)² = E_{μ⊗μ} Σ_W G_W(x) G_W(y)` (`family_sq`) and `Fintype.prod_sum`.
* `pow_S_le`: for `|u| ≤ 1`, `S(u)^c − 1 ≤ c·u + Bfeat d c·u²`.
* `featDev_le`: `featDev d μ c ≤ c·Mean μ + Bfeat d c·Ov2 μ`.
* `ov2_le_dir`: `Ov2 μ ≤ A/n` if `E_μ (v·x)² ≤ A/n` for every unit `v`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM frob)
open BstLean.Part36 (monoVal)
open BstLean.Part53 (error53_e0)

variable {n : ℕ}

/-- The overlap `u = x·y`. -/
def dotp (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- The monomial multiset of a word `w : Fin j → Fin n`. -/
def symOf {j : ℕ} (w : Fin j → Fin n) : Sym (Fin n) j :=
  ⟨Finset.univ.val.map w, by simp⟩

lemma monoVal_symOf (x : Fin n → ℝ) {j : ℕ} (w : Fin j → Fin n) :
    monoVal x (symOf w).1 = ∏ t, x (w t) := by
  simp [monoVal, symOf, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

lemma symOf_surj (j : ℕ) : Function.Surjective (symOf (n := n) (j := j)) := by
  intro s
  obtain ⟨l, hl⟩ := Quot.exists_rep s.1
  have hlen : l.length = j := by
    have h2 := s.2
    rw [← hl] at h2
    simpa using h2
  refine ⟨fun t => l.get ⟨t, by omega⟩, ?_⟩
  apply Subtype.ext
  change Finset.univ.val.map (fun t : Fin j => l.get ⟨t, by omega⟩) = s.1
  rw [Fin.univ_val_map, ← hl]
  change ((List.ofFn fun t : Fin j => l.get ⟨t, by omega⟩ : List (Fin n)) : Multiset (Fin n)) = (l : Multiset (Fin n))
  congr 1
  apply List.ext_get
  · simp [hlen]
  · intro m h1 h2
    simp

/-- A sum of nonnegative terms over the target of a surjection is at most the pulled-back sum. -/
lemma sum_le_sum_surj {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (π : α → β)
    (hπ : Function.Surjective π) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ b, g b ≤ ∑ a, g (π a) := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun a => g (π a))]
  apply Finset.sum_le_sum
  intro b _
  obtain ⟨a, rfl⟩ := hπ b
  have ha : a ∈ Finset.univ.filter (fun a' => π a' = π a) := by simp
  exact Finset.single_le_sum (f := fun a' => g (π a')) (fun a' _ => hg _) ha

lemma sphere_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ hf

/-- **Fubini for a finite family**: `Σ_ι (E_μ G_ι)² = E_{μ⊗μ} Σ_ι G_ι(x) G_ι(y)`. -/
lemma family_sq {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {ι : Type*} [Fintype ι]
    (G : ι → (Fin n → ℝ) → ℝ) (hG : ∀ i, Continuous (G i)) :
    ∑ i, (∫ x, G i x ∂μ) ^ 2 = ∫ z, ∑ i, G i z.1 * G i z.2 ∂(μ.prod μ) := by
  let := hμ.prob
  rw [integral_finset_sum _ (fun i _ =>
    (sphere_integrable hμ (hG i)).mul_prod (sphere_integrable hμ (hG i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod_mul, sq]

private lemma phiM_cont {d : ℕ} (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) :=
  continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)

/-- The word index of the monomials of degree `≤ d`. -/
abbrev Word (n d : ℕ) := Σ j : Fin (d + 1), (Fin j → Fin n)

/-- The monomial of a word. -/
def monoOf {d : ℕ} (a : Word n d) : Mono n d := ⟨a.1, symOf a.2⟩

lemma monoOf_surj (d : ℕ) : Function.Surjective (monoOf (n := n) (d := d)) := by
  rintro ⟨j, s⟩
  obtain ⟨w, hw⟩ := symOf_surj (n := n) j s
  exact ⟨⟨j, w⟩, by simp [monoOf, hw]⟩

lemma phiM_monoOf {d : ℕ} (x : Fin n → ℝ) (a : Word n d) :
    phiM x (monoOf a) = ∏ r, x (a.2 r) := monoVal_symOf x a.2

lemma monoOf_zero (d : ℕ) : monoOf (n := n) (d := d) ⟨0, Fin.elim0⟩ = default := by
  unfold monoOf
  change (⟨0, symOf Fin.elim0⟩ : Mono n d) = ⟨0, Sym.nil⟩
  congr 1

/-- `Σ_a Π_r x_{a r} y_{a r} = Σ_{j ≤ d} (x·y)^j`. -/
lemma word_sum (d : ℕ) (x y : Fin n → ℝ) :
    ∑ a : Word n d, ∏ r, (x (a.2 r) * y (a.2 r)) = ∑ j : Fin (d + 1), dotp x y ^ (j : ℕ) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  unfold dotp
  have h := Fintype.prod_sum (fun (_ : Fin j) (i : Fin n) => x i * y i)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]

/-- **Lemma O1, inequality form**: `featDev d μ c ≤ E_{μ⊗μ} (Σ_{j ≤ d} u^j)^c − 1`. -/
theorem featDev_le_overlap {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (d c : ℕ) :
    featDev d μ c ≤
      (∫ z, (∑ j : Fin (d + 1), dotp z.1 z.2 ^ (j : ℕ)) ^ c ∂(μ.prod μ)) - 1 := by
  classical
  let := hμ.prob
  let π : (Fin c → Word n d) → (Fin c → Mono n d) := fun W t => monoOf (W t)
  have hπ : Function.Surjective π := by
    intro p
    refine ⟨fun t => Classical.choose (monoOf_surj d (p t)), ?_⟩
    funext t
    exact Classical.choose_spec (monoOf_surj d (p t))
  let G : (Fin c → Word n d) → (Fin n → ℝ) → ℝ := fun W x => ∏ t, phiM x (π W t)
  have hG (W) : Continuous (G W) := continuous_finset_prod _ (fun t _ => phiM_cont _)
  let a : (Fin c → Word n d) → ℝ := fun W => ∫ x, G W x ∂μ
  let e : (Fin c → Word n d) → ℝ := fun W => ∏ t, error53_e0 (π W t)
  have he (W) : (a W - e W) ^ 2 = a W ^ 2 - e W ∧ 0 ≤ e W := by
    by_cases h : ∀ t, π W t = default
    · have h1 : e W = 1 := by simp [e, error53_e0, h]
      have h2 : a W = 1 := by
        have : G W = fun _ => 1 := by
          funext x
          simp only [G, h]
          exact Finset.prod_eq_one (fun t _ => rfl)
        simp [a, this]
      rw [h1, h2]; norm_num
    · push Not at h
      obtain ⟨t, ht⟩ := h
      have h1 : e W = 0 := Finset.prod_eq_zero (Finset.mem_univ t) (by simp [error53_e0, ht])
      rw [h1]; simp
  have hle : featDev d μ c ≤ ∑ W, (a W - e W) ^ 2 :=
    sum_le_sum_surj π hπ (fun p => ((∫ x, ∏ t, phiM x (p t) ∂μ) - ∏ t, error53_e0 (p t)) ^ 2)
      (fun _ => sq_nonneg _)
  have hW0 : e (fun _ => ⟨0, Fin.elim0⟩) = 1 := by
    simp [e, π, monoOf_zero, error53_e0]
  have hsum : ∑ W, (a W - e W) ^ 2 ≤ (∑ W, a W ^ 2) - 1 := by
    simp_rw [fun W => (he W).1]
    rw [Finset.sum_sub_distrib]
    have := Finset.single_le_sum (f := e) (fun W _ => (he W).2)
      (Finset.mem_univ (fun _ => ⟨0, Fin.elim0⟩ : Fin c → Word n d))
    rw [hW0] at this
    linarith
  have hfam := family_sq hμ G hG
  have hint (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      ∑ W, G W z.1 * G W z.2 = (∑ j : Fin (d + 1), dotp z.1 z.2 ^ (j : ℕ)) ^ c := by
    have h1 (W : Fin c → Word n d) : G W z.1 * G W z.2 =
        ∏ t, ∏ r, (z.1 ((W t).2 r) * z.2 ((W t).2 r)) := by
      simp only [G, π, phiM_monoOf, ← Finset.prod_mul_distrib]
    simp_rw [h1]
    rw [← Fintype.prod_sum (fun (_ : Fin c) (a : Word n d) => ∏ r, (z.1 (a.2 r) * z.2 (a.2 r)))]
    rw [word_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hint] at hfam
  calc featDev d μ c ≤ _ := hle
    _ ≤ _ := hsum
    _ = _ := by rw [← hfam]

/-! ## The polynomial inequality -/

lemma binom_rem (c : ℕ) (v A : ℝ) (hA : 0 ≤ A) (hv : |v| ≤ A) :
    |(1 + v) ^ c - 1 - c * v| ≤ (A + 2) ^ c * v ^ 2 := by
  induction c with
  | zero => simp; positivity
  | succ c ih =>
    have hc : (c : ℝ) ≤ (A + 2) ^ c := by
      have h1 : (c : ℝ) ≤ 2 ^ c := by exact_mod_cast (Nat.lt_two_pow_self).le
      exact h1.trans (pow_le_pow_left₀ (by norm_num) (by linarith) c)
    have he : (1 + v) ^ (c + 1) - 1 - ((c + 1 : ℕ) : ℝ) * v =
        (1 + v) * ((1 + v) ^ c - 1 - c * v) + c * v ^ 2 := by push_cast; ring
    rw [he]
    have h1v : |1 + v| ≤ A + 1 := by
      calc |1 + v| ≤ |1| + |v| := abs_add_le _ _
        _ ≤ A + 1 := by simp; linarith
    have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
    calc |(1 + v) * ((1 + v) ^ c - 1 - c * v) + c * v ^ 2|
        ≤ |1 + v| * |(1 + v) ^ c - 1 - c * v| + c * v ^ 2 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * v ^ 2)]
      _ ≤ (A + 1) * ((A + 2) ^ c * v ^ 2) + (A + 2) ^ c * v ^ 2 := by
          gcongr
      _ = (A + 2) ^ (c + 1) * v ^ 2 := by ring

lemma geom_bounds (d : ℕ) (hd : 1 ≤ d) (u : ℝ) (hu : |u| ≤ 1) :
    |(∑ j ∈ Finset.range (d + 1), u ^ j) - 1| ≤ d * |u| ∧
      |(∑ j ∈ Finset.range (d + 1), u ^ j) - 1 - u| ≤ d * u ^ 2 := by
  induction d with
  | zero => omega
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      simp [Finset.sum_range_succ]
      positivity
    · obtain ⟨h1, h2⟩ := ih hpos
      rw [Finset.sum_range_succ]
      have hp : |u ^ (d + 1)| ≤ u ^ 2 := by
        rw [abs_pow]
        calc |u| ^ (d + 1) = |u| ^ 2 * |u| ^ (d - 1) := by
              rw [← pow_add]; congr 1; omega
          _ ≤ |u| ^ 2 * 1 := by
              gcongr
              exact pow_le_one₀ (abs_nonneg u) hu
          _ = u ^ 2 := by rw [mul_one, sq_abs]
      have hp' : |u ^ (d + 1)| ≤ |u| := by
        rw [abs_pow]
        calc |u| ^ (d + 1) = |u| * |u| ^ d := by ring
          _ ≤ |u| * 1 := by gcongr; exact pow_le_one₀ (abs_nonneg u) hu
          _ = |u| := mul_one _
      push_cast
      constructor
      · calc |(∑ j ∈ Finset.range (d + 1), u ^ j) + u ^ (d + 1) - 1|
            ≤ |(∑ j ∈ Finset.range (d + 1), u ^ j) - 1| + |u ^ (d + 1)| := by
              rw [show (∑ j ∈ Finset.range (d + 1), u ^ j) + u ^ (d + 1) - 1 =
                ((∑ j ∈ Finset.range (d + 1), u ^ j) - 1) + u ^ (d + 1) by ring]
              exact abs_add_le _ _
          _ ≤ d * |u| + |u| := add_le_add h1 hp'
          _ = (d + 1) * |u| := by ring
      · calc |(∑ j ∈ Finset.range (d + 1), u ^ j) + u ^ (d + 1) - 1 - u|
            ≤ |(∑ j ∈ Finset.range (d + 1), u ^ j) - 1 - u| + |u ^ (d + 1)| := by
              rw [show (∑ j ∈ Finset.range (d + 1), u ^ j) + u ^ (d + 1) - 1 - u =
                ((∑ j ∈ Finset.range (d + 1), u ^ j) - 1 - u) + u ^ (d + 1) by ring]
              exact abs_add_le _ _
          _ ≤ d * u ^ 2 + u ^ 2 := add_le_add h2 hp
          _ = (d + 1) * u ^ 2 := by ring

/-- The constant of the quadratic term, `c·d + (d+2)^c·d²`. -/
noncomputable def Bfeat (d c : ℕ) : ℝ := c * d + ((d : ℝ) + 2) ^ c * (d : ℝ) ^ 2

lemma Bfeat_nonneg (d c : ℕ) : 0 ≤ Bfeat d c := by unfold Bfeat; positivity

/-- **The pointwise bound**: for `|u| ≤ 1`, `(Σ_{j ≤ d} u^j)^c − 1 ≤ c·u + Bfeat d c·u²`. -/
lemma pow_S_le (d c : ℕ) (hd : 1 ≤ d) (u : ℝ) (hu : |u| ≤ 1) :
    (∑ j : Fin (d + 1), u ^ (j : ℕ)) ^ c - 1 ≤ c * u + Bfeat d c * u ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => u ^ j)]
  set S := ∑ j ∈ Finset.range (d + 1), u ^ j
  obtain ⟨h1, h2⟩ := geom_bounds d hd u hu
  set v := S - 1
  have hvA : |v| ≤ d := h1.trans (by
    have : (d : ℝ) * |u| ≤ d * 1 := by gcongr
    linarith)
  have hb := binom_rem c v d (Nat.cast_nonneg d) hvA
  have hS : S = 1 + v := by simp [v]
  rw [hS]
  have hv2 : v ^ 2 ≤ (d : ℝ) ^ 2 * u ^ 2 := by
    have : |v| ^ 2 ≤ ((d : ℝ) * |u|) ^ 2 := by gcongr
    rw [sq_abs, mul_pow, sq_abs] at this
    exact this
  have hvu : (c : ℝ) * v ≤ c * u + c * (d * u ^ 2) := by
    have : v - u ≤ d * u ^ 2 := (le_abs_self _).trans (by simpa [v] using h2)
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith
  have hpow : (0 : ℝ) ≤ ((d : ℝ) + 2) ^ c := by positivity
  have hr : (1 + v) ^ c - 1 - c * v ≤ ((d : ℝ) + 2) ^ c * ((d : ℝ) ^ 2 * u ^ 2) :=
    (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left hv2 hpow))
  unfold Bfeat
  nlinarith

/-! ## Integration over `μ ⊗ μ` -/

/-- `Mean μ = Σ_i (E_μ x_i)²`. -/
noncomputable def Mean (μ : Measure (Fin n → ℝ)) : ℝ := ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2

/-- `Ov2 μ = E_{μ⊗μ} (x·y)²`. -/
noncomputable def Ov2 (μ : Measure (Fin n → ℝ)) : ℝ := ∫ z, dotp z.1 z.2 ^ 2 ∂(μ.prod μ)

lemma dotp_sq_le {x y : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) :
    dotp x y ^ 2 ≤ 1 := by
  unfold dotp
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  rw [hx, hy] at this
  simpa using this

lemma ae_pair {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) :
    ∀ᵐ z ∂(μ.prod μ), |dotp z.1 z.2| ≤ 1 := by
  let := hμ.prob
  have h1 : ∀ᵐ z ∂(μ.prod μ), ∑ i, z.1 i ^ 2 = 1 :=
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hμ.sphere
  have h2 : ∀ᵐ z ∂(μ.prod μ), ∑ i, z.2 i ^ 2 = 1 :=
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hμ.sphere
  filter_upwards [h1, h2] with z hz1 hz2
  have := dotp_sq_le hz1 hz2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (dotp z.1 z.2 + 1), sq_nonneg (dotp z.1 z.2 - 1)]

private lemma continuous_dotp : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => dotp z.1 z.2) := by
  unfold dotp; fun_prop

private lemma integrable_poly {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (P : ℝ → ℝ)
    (hP : Continuous P) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => P (dotp z.1 z.2)) (μ.prod μ) := by
  let := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).bddAbove_image
    hP.norm.continuousOn
  apply Integrable.of_bound (hP.comp continuous_dotp).aestronglyMeasurable C
  filter_upwards [ae_pair hμ] with z hz
  exact hC (Set.mem_image_of_mem _ (abs_le.mp hz))

lemma mean_eq {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) :
    Mean μ = ∫ z, dotp z.1 z.2 ∂(μ.prod μ) := by
  unfold Mean dotp
  exact family_sq hμ (fun i x => x i) (fun i => continuous_apply i)

lemma Ov2_nonneg (μ : Measure (Fin n → ℝ)) : 0 ≤ Ov2 μ :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- **The main-term tensors from overlap moments**: `featDev d μ c ≤ c·Mean μ + Bfeat d c·Ov2 μ`. -/
theorem featDev_le {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (d c : ℕ) (hd : 1 ≤ d) :
    featDev d μ c ≤ c * Mean μ + Bfeat d c * Ov2 μ := by
  let := hμ.prob
  have h := featDev_le_overlap hμ d c
  have hS : Continuous (fun u : ℝ => (∑ j : Fin (d + 1), u ^ (j : ℕ)) ^ c) := by fun_prop
  have hi1 := integrable_poly hμ _ hS
  have hi2 := integrable_poly hμ (fun u => (c : ℝ) * u + Bfeat d c * u ^ 2) (by fun_prop)
  have hmono : (∫ z, (∑ j : Fin (d + 1), dotp z.1 z.2 ^ (j : ℕ)) ^ c - 1 ∂(μ.prod μ)) ≤
      ∫ z, (c : ℝ) * dotp z.1 z.2 + Bfeat d c * dotp z.1 z.2 ^ 2 ∂(μ.prod μ) := by
    apply integral_mono_ae (hi1.sub (integrable_const 1)) hi2
    filter_upwards [ae_pair hμ] with z hz
    exact pow_S_le d c hd _ hz
  rw [integral_sub hi1 (integrable_const 1)] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmono
  have hu := integrable_poly hμ (fun u => u) continuous_id
  have hu2 := integrable_poly hμ (fun u => u ^ 2) (by fun_prop)
  rw [integral_add (hu.const_mul _) (hu2.const_mul _), integral_const_mul, integral_const_mul,
    ← mean_eq hμ] at hmono
  unfold Ov2
  linarith

/-- **`Ov2` from directional second moments.** -/
theorem ov2_le_dir {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (B : ℝ)
    (hdir : ∀ v : Fin n → ℝ, ∑ i, v i ^ 2 = 1 → ∫ x, (∑ i, v i * x i) ^ 2 ∂μ ≤ B) :
    Ov2 μ ≤ B := by
  let := hμ.prob
  have hi := integrable_poly hμ (fun u => u ^ 2) (by fun_prop)
  unfold Ov2
  rw [integral_prod _ hi]
  calc (∫ x, ∫ y, dotp (x, y).1 (x, y).2 ^ 2 ∂μ ∂μ) ≤ ∫ _x, B ∂μ := by
        apply integral_mono_ae hi.integral_prod_left (integrable_const B)
        filter_upwards [hμ.sphere] with x hx
        exact hdir x hx
    _ = B := by simp

/-- **The overlap form of the conditions gives `Good72`** (every `d ≥ 1`, every `k`):
from `Mean μ ≤ A/n`, directional second moments `≤ A/n`, and the trace moments for `2i ≤ k`,
`Good72 n d k μ w (Fov d A) A` with `Fov d A c = (c + Bfeat d c)·A`. -/
noncomputable def Fov (d : ℕ) (A : ℝ) (c : ℕ) : ℝ := ((c : ℝ) + Bfeat d c) * A

theorem good_of_ov {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (d k : ℕ) (hd : 1 ≤ d)
    (w : ℕ → ℝ) (A : ℝ)
    (hmean : Mean μ ≤ A / n)
    (hdir : ∀ v : Fin n → ℝ, ∑ i, v i ^ 2 = 1 → ∫ x, (∑ i, v i * x i) ^ 2 ∂μ ≤ A / n)
    (hdev : ∀ i : ℕ, 1 ≤ i → 2 * i ≤ k →
      (∫ x, (BstLean.Part41.phiSq d x - BstLean.Part53.c0 d) ^ (2 * i) ∂μ) ≤
        w i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i)) :
    Good72 n d k μ w (Fov d A) A := by
  refine ⟨hμ, hdev, ?_, hmean⟩
  intro c _ _
  have h1 := featDev_le hμ d c hd
  have h2 := ov2_le_dir hμ _ hdir
  have hB := Bfeat_nonneg d c
  calc featDev d μ c ≤ c * Mean μ + Bfeat d c * Ov2 μ := h1
    _ ≤ c * (A / n) + Bfeat d c * (A / n) := by gcongr
    _ = Fov d A c / n := by unfold Fov; ring

end BstLean.Part72
