import BstLean.Part53Defs
import BstLean.Part33Moments
import BstLean.Part36Index

/-!
# Part 53, wave 1: the elementary lemmas U, S, G, Tr (§3 of the source)

Specification: `delegations/answers/p53-spec-opus.md` §3.2.
All four lemmas are proved here (no `sorry`). Do not use `native_decide` or `axiom`
anywhere. This file imports `Part53Defs` only (a prover may also import finished Part 29–52 files,
but no other Part 53 wave-1 file).

Suggested route.
* `lemmaU53` (proved, by the multinomial theorem `Finset.sum_pow`, not by power sums): `z_i = x_i²` on the simplex; `u = Σ_{j ≤ d} h_j(z)` (complete homogeneous symmetric
  polynomials; each multiset once, as in `phiSq`). `h_j = Σ_{λ ⊢ j} p_λ/z_λ`, `Σ 1/z_λ = 1`, the
  partition `1^j` gives `1/j!`, and `0 ≤ p_λ ≤ p₂(z) = p₄(x)` for the others. A direct route: show
  `h_j(z) − 1/j! ≥ 0` and `≤ p₂(z)` by induction on `j` with `h_j = (1/j) Σ_{m=1}^j p_m h_{j−m}`.
* `lemmaS53` (proved, from Part 33's exact sphere moments `uniformSphere_prod` and `(2a−1)‼(2b−1)‼ ≤ (2a+2b−1)‼`; the source's route was: Gaussian polar factorization (Part 29's `uniformSphere` and its Gaussian representation,
  as in Part 47's `EW_le`), Minkowski in `L^q`, `E g^{4q} = (4q−1)!!`, `E‖g‖^{4q} ≥ n^{2q}`.
* `lemmaG53` (proved, by the variant below, for `d ≥ 2`). The source's route: split `a·φ` by degree, Cauchy–Schwarz over `d` degrees, the
  Gram matrix of Gaussian moments, row sums `≤ (2j−1)!! n^{⌊j/2⌋}` (parity of exponents),
  `E‖g‖^{2j} ≥ n^j`. A variant: Schur's test with `M_{pq} = E_σ x^{p+q} ≥ 0` (zero unless `p ≡ q mod 2`;
  Part 33's `uniformSphere_prod`), `R_p = E Σ_{q≡p} x^{p+q}`, and pointwise
  `Σ_{q≡p} |x^q| ≤ |x^r| Σ_{γ : Mono n d} z^γ ≤ (d+1)|x^r|` (`r` the odd part of `p`, `q = r + 2γ`,
  `hS53 z m ≤ 1` from the proof of Lemma U); so `R_p ≤ (d+1)/n` and the constant is `d + 1 ≤ cG d`.
* `lemmaTr53` (proved): Cauchy–Schwarz over the `nⁱ` contraction indices; `glue` is injective in `(c, w)` when
  `2i ≤ j`.
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount glue)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part29 (gaussMom)
open BstLean.Part36 (monoVal gpm rhoD)
open Finset

variable {n d : ℕ}

/-- `h_j(z) = Σ_{|s| = j} z^s`. -/
noncomputable def hS53 (z : Fin n → ℝ) (j : ℕ) : ℝ := ∑ s : Sym (Fin n) j, (s.1.map z).prod

private lemma multinomId53 (z : Fin n → ℝ) (j : ℕ) :
    (∑ i, z i) ^ j = ∑ s : Sym (Fin n) j, (s.1.countPerms : ℝ) * (s.1.map z).prod := by
  classical
  rw [Finset.sum_pow, Finset.sym_univ]

private lemma cpSpec53 (j : ℕ) (s : Sym (Fin n) j) :
    s.1.countPerms * ∏ i ∈ s.1.toFinset, (s.1.count i).factorial = j.factorial := by
  classical
  unfold Multiset.countPerms
  rw [Finsupp.multinomial_eq, mul_comm]
  have := Nat.multinomial_spec (s := s.1.toFinsupp.support) (f := s.1.toFinsupp)
  rw [Multiset.toFinsupp_support] at this ⊢
  simp only [Multiset.toFinsupp_apply] at this ⊢
  rw [this, Multiset.toFinset_sum_count_eq, s.2]

private lemma prodNonneg53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (m : Multiset (Fin n)) : 0 ≤ (m.map z).prod :=
  Multiset.prod_nonneg (fun a ha => by
    obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp ha
    exact hz b)

private lemma hSLeOne53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) : hS53 z j ≤ 1 := by
  classical
  have h := multinomId53 z j
  rw [h1, one_pow] at h
  rw [h]
  unfold hS53
  apply Finset.sum_le_sum
  intro s _
  have hcp : (1 : ℝ) ≤ s.1.countPerms := by
    have := Nat.multinomial_pos (s := s.1.toFinsupp.support) (f := s.1.toFinsupp)
    unfold Multiset.countPerms
    rw [Finsupp.multinomial_eq]
    exact_mod_cast this
  exact le_mul_of_one_le_left (prodNonneg53 z hz _) hcp


private lemma filterSum53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (i : Fin n) (j : ℕ) :
    ∑ s ∈ (Finset.univ : Finset (Sym (Fin n) j)).filter (fun s => 2 ≤ s.1.count i), (s.1.map z).prod ≤
      z i ^ 2 * hS53 z (j - 2) := by
  classical
  rcases lt_or_ge j 2 with hj | hj
  · have : (Finset.univ : Finset (Sym (Fin n) j)).filter (fun s => 2 ≤ s.1.count i) = ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_le]
      have := Multiset.count_le_card i s.1
      rw [s.2] at this
      omega
    rw [this, Finset.sum_empty]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun s _ => prodNonneg53 z hz _)
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    set g : Sym (Fin n) m → Sym (Fin n) (m + 2) := fun s' => i ::ₛ i ::ₛ s' with hg
    have hginj : Function.Injective g := by
      intro a b h
      exact (Sym.cons_inj_right _ _ _).mp ((Sym.cons_inj_right _ _ _).mp h)
    have himg : (Finset.univ : Finset (Sym (Fin n) (m + 2))).filter (fun s => 2 ≤ s.1.count i) =
        Finset.univ.image g := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hc
        have h1 : i ∈ s := Multiset.count_pos.mp (by omega)
        have h2 : i ∈ s.erase i h1 := by
          show i ∈ ((s.erase i h1 : Sym (Fin n) (m + 1)) : Multiset (Fin n))
          rw [Sym.coe_erase, ← Multiset.count_pos, Multiset.count_erase_self]
          exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hc)
        exact ⟨(s.erase i h1).erase i h2, by rw [hg]; simp only; rw [Sym.cons_erase, Sym.cons_erase]⟩
      · rintro ⟨s', rfl⟩
        show 2 ≤ Multiset.count i (((i ::ₛ i ::ₛ s') : Sym (Fin n) (m + 2)) : Multiset (Fin n))
        rw [Sym.coe_cons, Sym.coe_cons, Multiset.count_cons_self, Multiset.count_cons_self]
        omega
    rw [himg, Finset.sum_image (fun a _ b _ h => hginj h), Nat.add_sub_cancel]
    unfold hS53
    rw [Finset.mul_sum]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro s' _
    show ((((i ::ₛ i ::ₛ s') : Sym (Fin n) (m + 2)) : Multiset (Fin n)).map z).prod = _
    rw [Sym.coe_cons, Sym.coe_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, pow_two, mul_assoc]
    rfl


private lemma hSBounds53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) :
    1 / (j.factorial : ℝ) ≤ hS53 z j ∧ hS53 z j ≤ 1 / (j.factorial : ℝ) + ∑ i, z i ^ 2 := by
  classical
  have hid := multinomId53 z j
  rw [h1, one_pow] at hid
  have hjf : (0 : ℝ) < j.factorial := by positivity
  have hP1 : ∀ s : Sym (Fin n) j, 1 ≤ ∏ i ∈ s.1.toFinset, (s.1.count i).factorial :=
    fun s => Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
  have hcp_le : ∀ s : Sym (Fin n) j, (s.1.countPerms : ℝ) ≤ j.factorial := by
    intro s
    have h := cpSpec53 j s
    have : s.1.countPerms ≤ j.factorial := by
      rw [← h]; exact Nat.le_mul_of_pos_right _ (hP1 s)
    exact_mod_cast this
  have hpn : ∀ s : Sym (Fin n) j, 0 ≤ (s.1.map z).prod := fun s => prodNonneg53 z hz _
  constructor
  · rw [div_le_iff₀ hjf, hid]
    unfold hS53
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    nlinarith [hcp_le s, hpn s]
  · -- `j!·h − 1 = Σ (j! − cp) z^s`
    have key : ∀ s : Sym (Fin n) j, ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod ≤
        (j.factorial : ℝ) * ∑ i, if 2 ≤ s.1.count i then (s.1.map z).prod else 0 := by
      intro s
      by_cases hA : ∀ i, s.1.count i ≤ 1
      · have hP : ∏ i ∈ s.1.toFinset, (s.1.count i).factorial = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          have h1' : 1 ≤ s.1.count i := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hi)
          have : s.1.count i = 1 := le_antisymm (hA i) h1'
          rw [this, Nat.factorial_one]
        have h := cpSpec53 j s
        rw [hP, mul_one] at h
        rw [h, sub_self, zero_mul]
        exact mul_nonneg hjf.le (Finset.sum_nonneg fun i _ => by split_ifs; exact hpn s; exact le_rfl)
      · push Not at hA
        obtain ⟨i0, hi0⟩ := hA
        have hsum : (s.1.map z).prod ≤ ∑ i, if 2 ≤ s.1.count i then (s.1.map z).prod else 0 := by
          have := Finset.single_le_sum (f := fun i => if 2 ≤ s.1.count i then (s.1.map z).prod else 0)
            (fun i _ => by split_ifs; exact hpn s; exact le_rfl) (Finset.mem_univ i0)
          have h2 : 2 ≤ s.1.count i0 := hi0
          simp only [h2, ↓reduceIte] at this
          exact this
        have hcp0 : (0 : ℝ) ≤ s.1.countPerms := by positivity
        calc ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod ≤ (j.factorial : ℝ) * (s.1.map z).prod :=
              mul_le_mul_of_nonneg_right (by linarith) (hpn s)
          _ ≤ _ := mul_le_mul_of_nonneg_left hsum hjf.le
    have hsumkey := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Sym (Fin n) j))) => key s)
    have hlhs : ∑ s : Sym (Fin n) j, ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod =
        (j.factorial : ℝ) * hS53 z j - 1 := by
      rw [hid]; unfold hS53
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro s _; ring
    have hrhs : ∑ s : Sym (Fin n) j, (j.factorial : ℝ) * ∑ i, (if 2 ≤ s.1.count i then (s.1.map z).prod else 0) ≤
        (j.factorial : ℝ) * ∑ i, z i ^ 2 := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hjf.le
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter]
      calc _ ≤ z i ^ 2 * hS53 z (j - 2) := filterSum53 z hz i j
        _ ≤ z i ^ 2 * 1 := mul_le_mul_of_nonneg_left (hSLeOne53 z hz h1 _) (sq_nonneg _)
        _ = z i ^ 2 := mul_one _
    rw [hlhs] at hsumkey
    have : (j.factorial : ℝ) * hS53 z j ≤ 1 + (j.factorial : ℝ) * ∑ i, z i ^ 2 := by linarith
    rw [div_add' _ _ _ hjf.ne', le_div_iff₀ hjf]
    linarith

private lemma hSZero53 (z : Fin n → ℝ) : hS53 z 0 = 1 := by
  unfold hS53
  rw [Fintype.sum_unique]
  simp [Sym.eq_nil_of_card_zero]

/-- **Lemma U** (proved). -/
theorem lemmaU53 (d : ℕ) : LemmaU53 d := by
  classical
  intro n x hx
  set z : Fin n → ℝ := fun i => x i ^ 2 with hzdef
  have hz : ∀ i, 0 ≤ z i := fun i => sq_nonneg _
  have h1 : ∑ i, z i = 1 := hx
  have hphi : phiSq d x = ∑ i : Fin (d + 1), hS53 z i := by
    unfold phiSq phiM hS53
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro s _
    unfold BstLean.Part36.monoVal
    rw [hzdef, Multiset.prod_map_pow]
  have hc0 : c0 d = ∑ i : Fin (d + 1), 1 / ((i : ℕ).factorial : ℝ) := by
    unfold c0; rw [Fin.sum_univ_eq_sum_range (fun i => 1 / (i.factorial : ℝ))]
  have hp4 : p4 x = ∑ i, z i ^ 2 := by
    unfold p4; apply Finset.sum_congr rfl; intro i _; rw [hzdef]; ring
  rw [hphi, hc0, hp4, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg fun i _ => by linarith [(hSBounds53 z hz h1 i).1]
  · rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, div_one, hSZero53, sub_self, zero_add]
    calc ∑ i : Fin d, (hS53 z (i.succ : ℕ) - 1 / (((i.succ : Fin (d + 1)) : ℕ).factorial : ℝ))
        ≤ ∑ _i : Fin d, ∑ i, z i ^ 2 :=
          Finset.sum_le_sum fun i _ => by linarith [(hSBounds53 z hz h1 (i.succ : ℕ)).2]
      _ = d * ∑ i, z i ^ 2 := by simp

private def E53 (a : ℕ) : ℕ := (2 * a - 1).doubleFactorial

private lemma E53_succ (b : ℕ) : E53 (b + 1) = (2 * b + 1) * E53 b := by
  unfold E53
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [show 2 * (c + 1 + 1) - 1 = (2 * c + 1) + 2 by omega, Nat.doubleFactorial_add_two,
      show 2 * (c + 1) - 1 = 2 * c + 1 by omega]
    ring

private lemma E53_mul (a b : ℕ) : E53 a * E53 b ≤ E53 (a + b) := by
  induction b with
  | zero => simp [E53]
  | succ b ih =>
    rw [E53_succ, ← add_assoc, E53_succ]
    calc E53 a * ((2 * b + 1) * E53 b) = (2 * b + 1) * (E53 a * E53 b) := by ring
      _ ≤ (2 * (a + b) + 1) * E53 (a + b) := Nat.mul_le_mul (by omega) ih

private lemma E53_prod {ι : Type*} (s : Finset ι) (c : ι → ℕ) :
    ∏ i ∈ s, E53 (c i) ≤ E53 (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E53]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact le_trans (Nat.mul_le_mul_left _ ih) (E53_mul _ _)

private lemma gaussMom4 (m : ℕ) : gaussMom (4 * m) = (E53 (2 * m) : ℝ) := by
  unfold gaussMom E53
  simp only [show Even (4 * m) from ⟨2 * m, by ring⟩, ↓reduceIte]
  congr 2
  omega


private lemma card_tau {n q : ℕ} (w : Fin q → Fin n) (i : Fin n) :
    (Finset.univ.filter fun s : Fin (q * 4) => w (finProdFinEquiv.symm s).1 = i).card =
      4 * (Finset.univ.filter fun a : Fin q => w a = i).card := by
  classical
  have h1 : (Finset.univ.filter fun s : Fin (q * 4) => w (finProdFinEquiv.symm s).1 = i).card =
      (Finset.univ.filter fun ab : Fin q × Fin 4 => w ab.1 = i).card := by
    apply Finset.card_bij (fun s _ => finProdFinEquiv.symm s)
    · intro s hs; simpa using hs
    · intro a _ b _ h; exact finProdFinEquiv.symm.injective h
    · intro ab hab
      refine ⟨finProdFinEquiv ab, ?_, by simp only [Equiv.symm_apply_apply]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact (Finset.mem_filter.mp hab).2
  rw [h1]
  have h2 : (Finset.univ.filter fun ab : Fin q × Fin 4 => w ab.1 = i) =
      (Finset.univ.filter fun a : Fin q => w a = i) ×ˢ (Finset.univ : Finset (Fin 4)) := by
    ext ab; simp
  rw [h2, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- **Lemma S** (proved). -/
theorem lemmaS53 : LemmaS53 := by
  classical
  intro n hn q hq
  have hS53 := BstLean.Part33.uniformSphere_prod n (q * 4) hn
  set τ : (Fin q → Fin n) → Fin (q * 4) → Fin n := fun w s => w (finProdFinEquiv.symm s).1 with hτ
  have hprod : ∀ (x : Fin n → ℝ) (w : Fin q → Fin n), ∏ t, x (w t) ^ 4 = ∏ s, x (τ w s) := by
    intro x w
    rw [← Fintype.prod_equiv finProdFinEquiv (fun ab : Fin q × Fin 4 => x (w ab.1)) (fun s => x (τ w s))
      (fun ab => by simp only [hτ, Equiv.symm_apply_apply]), Fintype.prod_prod_type]
    simp
  have hexp : ∀ x : Fin n → ℝ, p4 x ^ q = ∑ w : Fin q → Fin n, ∏ s, x (τ w s) := by
    intro x
    unfold p4
    rw [Fintype.sum_pow]
    exact Finset.sum_congr rfl fun w _ => hprod x w
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun w _ => hS53.integ (q * 4) le_rfl (τ w))]
  have hden : (n : ℝ) ^ (2 * q) ≤ ∏ j ∈ Finset.range (q * 4 / 2), ((n : ℝ) + 2 * j) := by
    rw [show q * 4 / 2 = 2 * q by omega]
    calc (n : ℝ) ^ (2 * q) = ∏ _j ∈ Finset.range (2 * q), (n : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith)
  have hnpos : (0 : ℝ) < (n : ℝ) ^ (2 * q) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hterm : ∀ w : Fin q → Fin n, ∫ x, ∏ s, x (τ w s) ∂uniformSphere n ≤
      ((4 * q - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * q) := by
    intro w
    rw [hS53.mom (q * 4) le_rfl (τ w)]
    have hnum : ∏ i, gaussMom (Finset.univ.filter fun s => τ w s = i).card ≤
        ((4 * q - 1).doubleFactorial : ℝ) := by
      have hc : ∀ i, gaussMom (Finset.univ.filter fun s => τ w s = i).card =
          (E53 (2 * (Finset.univ.filter fun a : Fin q => w a = i).card) : ℝ) := by
        intro i
        rw [show (Finset.univ.filter fun s => τ w s = i) =
          (Finset.univ.filter fun s : Fin (q * 4) => w (finProdFinEquiv.symm s).1 = i) from rfl,
          card_tau, gaussMom4]
      simp_rw [hc]
      rw [← Nat.cast_prod]
      have hsum : ∑ i, 2 * (Finset.univ.filter fun a : Fin q => w a = i).card = 2 * q := by
        rw [← Finset.mul_sum, ← Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (w a)),
          Finset.card_univ, Fintype.card_fin]
      have := E53_prod Finset.univ (fun i => 2 * (Finset.univ.filter fun a : Fin q => w a = i).card)
      rw [hsum] at this
      have h4 : E53 (2 * q) = (4 * q - 1).doubleFactorial := by
        unfold E53; congr 1; omega
      rw [h4] at this
      exact_mod_cast this
    have hnum0 : 0 ≤ ∏ i, gaussMom (Finset.univ.filter fun s => τ w s = i).card := by
      apply Finset.prod_nonneg; intro i _; unfold gaussMom; split_ifs <;> positivity
    calc _ ≤ ((4 * q - 1).doubleFactorial : ℝ) / ∏ j ∈ Finset.range (q * 4 / 2), ((n : ℝ) + 2 * j) :=
          div_le_div_of_nonneg_right hnum (lt_of_lt_of_le hnpos hden).le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hnpos hden
  calc ∑ w : Fin q → Fin n, ∫ x, ∏ s, x (τ w s) ∂uniformSphere n
      ≤ ∑ _w : Fin q → Fin n, ((4 * q - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * q) :=
        Finset.sum_le_sum fun w _ => hterm w
    _ = ((4 * q - 1).doubleFactorial : ℝ) / (n : ℝ) ^ q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        have : (0 : ℝ) < n := by exact_mod_cast hn
        rw [show 2 * q = q + q by ring, pow_add]
        field_simp
        push_cast [Fintype.card_fin]
        ring

private lemma prodMapUniv (f : Fin n → ℝ) (u : Multiset (Fin n)) :
    (u.map f).prod = ∏ i, f i ^ u.count i := by
  classical
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Multiset.count_eq_zero.mpr (by simpa using hi), pow_zero]

private lemma gpm_nonneg (u : Multiset (Fin n)) : 0 ≤ gpm u := by
  unfold gpm
  apply Finset.prod_nonneg; intro i _
  unfold gaussMom; split_ifs <;> positivity

private lemma rhoD_pos (hn : 1 ≤ n) (r : ℕ) : 0 < rhoD n r := by
  unfold rhoD
  apply Finset.prod_pos; intro j _
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

private lemma mom (hn : 1 ≤ n) (u : Multiset (Fin n)) :
    Integrable (fun x => monoVal x u) (uniformSphere n) ∧
      ∫ x, monoVal x u ∂uniformSphere n = gpm u / rhoD n (Multiset.card u / 2) :=
  BstLean.Part36.sphere_multiset (uniformSphere n) (BstLean.Part33.uniformSphere_prod n _ hn) u le_rfl

private lemma mom_nonneg (hn : 1 ≤ n) (u : Multiset (Fin n)) : 0 ≤ ∫ x, monoVal x u ∂uniformSphere n := by
  rw [(mom hn u).2]; exact div_nonneg (gpm_nonneg u) (rhoD_pos hn _).le

private lemma mom_odd (hn : 1 ≤ n) (u : Multiset (Fin n)) (h : ∃ i, ¬ Even (u.count i)) :
    ∫ x, monoVal x u ∂uniformSphere n = 0 := by
  rw [(mom hn u).2]
  obtain ⟨i, hi⟩ := h
  have : gpm u = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gaussMom, hi])
  rw [this, zero_div]

private lemma mom_sq (hn : 1 ≤ n) (i : Fin n) : ∫ x, x i ^ 2 ∂uniformSphere n = 1 / n := by
  classical
  have h := (mom hn ({i, i} : Multiset (Fin n))).2
  have e : ∀ x : Fin n → ℝ, monoVal x ({i, i} : Multiset (Fin n)) = x i ^ 2 := by
    intro x; simp [monoVal, sq]
  simp_rw [e] at h
  rw [h]
  have hg : gpm ({i, i} : Multiset (Fin n)) = 1 := by
    unfold gpm
    rw [Finset.prod_eq_single i]
    · simp [gaussMom]
    · intro j _ hj
      simp [gaussMom, Multiset.count_singleton, hj]
    · simp
  have hr : rhoD n (Multiset.card ({i, i} : Multiset (Fin n)) / 2) = n := by
    simp [rhoD]
  rw [hg, hr]


private noncomputable def oddP (u : Multiset (Fin n)) (x : Fin n → ℝ) : ℝ := ∏ i, |x i| ^ (u.count i % 2)

private noncomputable def gam (u : Multiset (Fin n)) : Multiset (Fin n) :=
  (Finset.univ : Finset (Fin n)).val.bind (fun i => Multiset.replicate (u.count i / 2) i)

private lemma count_gam (u : Multiset (Fin n)) (j : Fin n) : (gam u).count j = u.count j / 2 := by
  classical
  unfold gam
  rw [Multiset.count_bind]
  rw [show ((Finset.univ : Finset (Fin n)).val.map fun i => Multiset.count j (Multiset.replicate (u.count i / 2) i)).sum
      = ∑ i, Multiset.count j (Multiset.replicate (u.count i / 2) i) from rfl]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Multiset.count_replicate, hij, Ne.symm hij]
  · simp

private lemma card_gam_le (u : Multiset (Fin n)) : Multiset.card (gam u) ≤ Multiset.card u := by
  classical
  have h1 : Multiset.card (gam u) = ∑ i, (gam u).count i := (Multiset.sum_count_eq_card (by simp)).symm
  have h2 : Multiset.card u = ∑ i, u.count i := (Multiset.sum_count_eq_card (by simp)).symm
  rw [h1, h2]
  apply Finset.sum_le_sum; intro i _
  rw [count_gam]; exact Nat.div_le_self _ _

private lemma abs_mono_split (u : Multiset (Fin n)) (x : Fin n → ℝ) :
    |monoVal x u| = oddP u x * monoVal (fun i => x i ^ 2) (gam u) := by
  classical
  unfold monoVal oddP
  rw [prodMapUniv, prodMapUniv, Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  rw [count_gam, abs_pow]
  conv_lhs => rw [← Nat.mod_add_div (u.count i) 2]
  rw [pow_add, pow_mul, sq_abs]

private lemma mono_ext (p q : Mono n d) (h : (p.2 : Multiset (Fin n)) = (q.2 : Multiset (Fin n))) : p = q := by
  obtain ⟨i, s⟩ := p
  obtain ⟨j, t⟩ := q
  have hij : i = j := by
    apply Fin.ext
    have hs := s.2
    have ht := t.2
    simp only at h
    calc (i : ℕ) = Multiset.card (s : Multiset (Fin n)) := hs.symm
      _ = Multiset.card (t : Multiset (Fin n)) := congrArg _ h
      _ = j := ht
  subst hij
  have : s = t := Subtype.ext h
  subst this
  rfl

private lemma class_bound (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (x : Fin n → ℝ)
    (hxz : ∀ i, z i = x i ^ 2) (p : Mono n d) :
    ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
      |monoVal x q.2.1| ≤ oddP p.2.1 x * (d + 1) := by
  classical
  have hzx : (fun i => x i ^ 2) = z := funext fun i => (hxz i).symm
  let emb : Mono n d → Mono n d := fun q =>
    ⟨⟨Multiset.card (gam q.2.1), lt_of_le_of_lt (card_gam_le q.2.1) (by rw [q.2.2]; exact q.1.2)⟩,
      ⟨gam q.2.1, rfl⟩⟩
  have hinj : Set.InjOn emb ((Finset.univ : Finset (Mono n d)).filter
      (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)) := by
    intro q hq q' hq' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq hq'
    have hg : gam q.2.1 = gam q'.2.1 := congrArg (fun g : Mono n d => (g.2 : Multiset (Fin n))) he
    apply mono_ext
    ext i
    show q.2.1.count i = q'.2.1.count i
    have h2 := congrArg (fun m => m.count i) hg
    simp only [count_gam] at h2
    have := Nat.mod_add_div (q.2.1.count i) 2
    have := Nat.mod_add_div (q'.2.1.count i) 2
    have := hq i
    have := hq' i
    omega
  have hsum : ∑ g : Mono n d, monoVal z g.2.1 ≤ d + 1 := by
    rw [Fintype.sum_sigma]
    calc ∑ m : Fin (d + 1), ∑ s : Sym (Fin n) m, monoVal z s.1
        ≤ ∑ _m : Fin (d + 1), (1 : ℝ) := Finset.sum_le_sum fun m _ => hSLeOne53 z hz h1 m
      _ = d + 1 := by simp
  have hoddp : 0 ≤ oddP p.2.1 x := by unfold oddP; positivity
  calc ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
        |monoVal x q.2.1|
      ≤ ∑ g : Mono n d, oddP p.2.1 x * monoVal z g.2.1 := by
        apply Finset.sum_le_sum_of_injOn emb hinj (Finset.subset_univ _)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [abs_mono_split, hzx]
          have : oddP q.2.1 x = oddP p.2.1 x := by
            unfold oddP; apply Finset.prod_congr rfl; intro i _; rw [hq i]
          rw [this]
        · intro g _ _
          exact mul_nonneg hoddp (Multiset.prod_nonneg fun a ha => by
            obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp ha; exact hz b)
    _ = oddP p.2.1 x * ∑ g : Mono n d, monoVal z g.2.1 := by rw [Finset.mul_sum]
    _ ≤ oddP p.2.1 x * (d + 1) := mul_le_mul_of_nonneg_left hsum hoddp

private lemma prod_le_one_factor (f : Fin n → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) (i : Fin n) :
    ∏ j, f j ≤ f i := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, f j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (hf j).1) (fun j _ => (hf j).2)
  have h0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j := Finset.prod_nonneg fun j _ => (hf j).1
  nlinarith [(hf i).1]

private lemma abs_le_one_of_sphere {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (j : Fin n) : |x j| ≤ 1 := by
  have := Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  rw [hx] at this
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

private lemma L4 (p : Mono n d) (hp : p ≠ default) :
    ∃ i : Fin n, ∀ x : Fin n → ℝ, ∑ j, x j ^ 2 = 1 → |monoVal x p.2.1| * oddP p.2.1 x ≤ x i ^ 2 := by
  classical
  have habs : ∀ x : Fin n → ℝ, |monoVal x p.2.1| = ∏ j, |x j| ^ p.2.1.count j := by
    intro x; unfold monoVal; rw [prodMapUniv, Finset.abs_prod]; simp [abs_pow]
  by_cases hodd : ∃ i, p.2.1.count i % 2 = 1
  · obtain ⟨i, hi⟩ := hodd
    refine ⟨i, fun x hx => ?_⟩
    have hb : ∀ j, 0 ≤ |x j| ∧ |x j| ≤ 1 := fun j => ⟨abs_nonneg _, abs_le_one_of_sphere hx j⟩
    have h1 : |monoVal x p.2.1| ≤ |x i| := by
      rw [habs]
      calc ∏ j, |x j| ^ p.2.1.count j ≤ |x i| ^ p.2.1.count i :=
            prod_le_one_factor _ (fun j => ⟨pow_nonneg (hb j).1 _, pow_le_one₀ (hb j).1 (hb j).2⟩) i
        _ ≤ |x i| := pow_le_of_le_one (hb i).1 (hb i).2 (by omega)
    have h2 : oddP p.2.1 x ≤ |x i| := by
      unfold oddP
      calc ∏ j, |x j| ^ (p.2.1.count j % 2) ≤ |x i| ^ (p.2.1.count i % 2) :=
            prod_le_one_factor _ (fun j => ⟨pow_nonneg (hb j).1 _, pow_le_one₀ (hb j).1 (hb j).2⟩) i
        _ = |x i| := by rw [hi, pow_one]
    have h3 : 0 ≤ oddP p.2.1 x := by unfold oddP; positivity
    calc |monoVal x p.2.1| * oddP p.2.1 x ≤ |x i| * |x i| :=
          mul_le_mul h1 h2 h3 (abs_nonneg _)
      _ = x i ^ 2 := by rw [← sq, sq_abs]
  · push Not at hodd
    have hcard : 1 ≤ Multiset.card p.2.1 := by
      by_contra h0
      push Not at h0
      apply hp
      apply mono_ext
      have : Multiset.card p.2.1 = 0 := by omega
      show p.2.1 = (default : Mono n d).2.1
      rw [Multiset.card_eq_zero.mp this]
      rfl
    obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card p.2.1)
    have hci : 2 ≤ p.2.1.count i := by
      have h1 := Multiset.count_pos.mpr hi
      have h2 := hodd i
      omega
    refine ⟨i, fun x hx => ?_⟩
    have hb : ∀ j, 0 ≤ |x j| ∧ |x j| ≤ 1 := fun j => ⟨abs_nonneg _, abs_le_one_of_sphere hx j⟩
    have hoddP : oddP p.2.1 x = 1 := by
      unfold oddP
      apply Finset.prod_eq_one; intro j _
      have := hodd j
      have : p.2.1.count j % 2 = 0 := by omega
      rw [this, pow_zero]
    rw [hoddP, mul_one, habs]
    calc ∏ j, |x j| ^ p.2.1.count j ≤ |x i| ^ p.2.1.count i :=
          prod_le_one_factor _ (fun j => ⟨pow_nonneg (hb j).1 _, pow_le_one₀ (hb j).1 (hb j).2⟩) i
      _ ≤ |x i| ^ 2 := pow_le_pow_of_le_one (hb i).1 (hb i).2 hci
      _ = x i ^ 2 := sq_abs _

private lemma monoVal_add (x : Fin n → ℝ) (u v : Multiset (Fin n)) :
    monoVal x (u + v) = monoVal x u * monoVal x v := by
  unfold monoVal; rw [Multiset.map_add, Multiset.prod_add]

private noncomputable def Mpq (p q : Mono n d) : ℝ := ∫ x, monoVal x (p.2.1 + q.2.1) ∂uniformSphere n

private lemma Rp_bound (hn : 1 ≤ n) (p : Mono n d) (hp : p ≠ default) :
    ∑ q : Mono n d, Mpq p q ≤ (d + 1) / n := by
  classical
  set cls := (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : Mono n d => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)]
  have hzero : ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter
      (fun q => ¬ ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2), Mpq p q = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    push Not at hq
    obtain ⟨i, hi⟩ := hq
    apply mom_odd hn
    refine ⟨i, ?_⟩
    rw [Multiset.count_add, Nat.even_add]
    intro h
    apply hi
    rcases Nat.even_or_odd (p.2.1.count i) with he | ho
    · have := h.mp he
      rw [Nat.even_iff.mp he, Nat.even_iff.mp this]
    · have h' : ¬ Even (q.2.1.count i) := fun hq => (Nat.not_even_iff_odd.mpr ho) (h.mpr hq)
      rw [Nat.odd_iff.mp ho, Nat.odd_iff.mp (Nat.not_even_iff_odd.mp h')]
  rw [hzero, add_zero]
  obtain ⟨i, hi⟩ := L4 p hp
  have hint : ∀ q : Mono n d, Integrable (fun x => monoVal x p.2.1 * monoVal x q.2.1) (uniformSphere n) := by
    intro q
    simp_rw [← monoVal_add]
    exact (mom hn _).1
  have hsq : Integrable (fun x : Fin n → ℝ => x i ^ 2) (uniformSphere n) := by
    have := (mom hn ({i, i} : Multiset (Fin n))).1
    have e : ∀ x : Fin n → ℝ, monoVal x ({i, i} : Multiset (Fin n)) = x i ^ 2 := by
      intro x; simp [monoVal, sq]
    simpa only [e] using this
  have hz : ∀ x : Fin n → ℝ, ∑ j, x j ^ 2 = 1 → ∀ j, 0 ≤ x j ^ 2 := fun _ _ j => sq_nonneg _
  calc ∑ q ∈ cls, Mpq p q = ∫ x, ∑ q ∈ cls, monoVal x p.2.1 * monoVal x q.2.1 ∂uniformSphere n := by
        rw [integral_finsetSum _ fun q _ => hint q]
        apply Finset.sum_congr rfl; intro q _
        unfold Mpq; simp_rw [monoVal_add]
    _ ≤ ∫ x, ((d : ℝ) + 1) * x i ^ 2 ∂uniformSphere n := by
        apply integral_mono_ae (integrable_finsetSum _ fun q _ => hint q) (hsq.const_mul _)
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
        have hcb := class_bound (d := d) (fun j => x j ^ 2) (fun j => sq_nonneg _) hx x (fun _ => rfl) p
        calc ∑ q ∈ cls, monoVal x p.2.1 * monoVal x q.2.1
            ≤ ∑ q ∈ cls, |monoVal x p.2.1| * |monoVal x q.2.1| :=
              Finset.sum_le_sum fun q _ => by rw [← abs_mul]; exact le_abs_self _
          _ = |monoVal x p.2.1| * ∑ q ∈ cls, |monoVal x q.2.1| := by rw [Finset.mul_sum]
          _ ≤ |monoVal x p.2.1| * (oddP p.2.1 x * (d + 1)) :=
              mul_le_mul_of_nonneg_left hcb (abs_nonneg _)
          _ = (d + 1) * (|monoVal x p.2.1| * oddP p.2.1 x) := by ring
          _ ≤ (d + 1) * x i ^ 2 := mul_le_mul_of_nonneg_left (hi x hx) (by positivity)
    _ = (d + 1) / n := by rw [integral_const_mul, mom_sq hn i]; ring

private lemma Mpq_symm (p q : Mono n d) : Mpq p q = Mpq q p := by
  unfold Mpq; rw [add_comm]

private lemma cG_ge (d : ℕ) (hd : 2 ≤ d) : (d : ℝ) + 1 ≤ cG d := by
  unfold cG
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have h : 2 * (m + 2) - 1 = (2 * m + 1) + 2 := by omega
  have hdf : (2 * (m + 2) - 1).doubleFactorial ≥ 2 * m + 3 := by
    rw [h, Nat.doubleFactorial_add_two]
    have := Nat.doubleFactorial_pos (2 * m + 1)
    nlinarith
  have : ((2 * (m + 2) - 1).doubleFactorial : ℝ) ≥ 2 * m + 3 := by exact_mod_cast hdf
  push_cast
  nlinarith

/-- **Lemma G** (proved, constant `d + 1 ≤ c_d`). -/
theorem lemmaG53 (d : ℕ) (hd : 2 ≤ d) : LemmaG53 d := by
  classical
  intro n hn a ha0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hint : ∀ p q : Mono n d, Integrable (fun x => a p * a q * monoVal x (p.2.1 + q.2.1)) (uniformSphere n) :=
    fun p q => (mom hn _).1.const_mul _
  have hexp : ∀ x : Fin n → ℝ, (∑ p, a p * phiM x p) ^ 2 =
      ∑ p, ∑ q, a p * a q * monoVal x (p.2.1 + q.2.1) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [monoVal_add]; unfold phiM; ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  simp_rw [integral_finsetSum _ fun q _ => hint _ q, integral_const_mul]
  have hM0 : ∀ p q : Mono n d, 0 ≤ Mpq p q := fun p q => mom_nonneg hn _
  calc ∑ p, ∑ q, a p * a q * ∫ x, monoVal x (p.2.1 + q.2.1) ∂uniformSphere n
      ≤ ∑ p : Mono n d, ∑ q : Mono n d, ((a p ^ 2 + a q ^ 2) / 2) * Mpq p q := by
        apply Finset.sum_le_sum; intro p _
        apply Finset.sum_le_sum; intro q _
        apply mul_le_mul_of_nonneg_right _ (hM0 p q)
        nlinarith [sq_nonneg (a p - a q)]
    _ = ∑ p : Mono n d, a p ^ 2 * ∑ q : Mono n d, Mpq p q := by
        have e1 : ∑ p : Mono n d, ∑ q : Mono n d, ((a p ^ 2 + a q ^ 2) / 2) * Mpq p q =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * Mpq p q) +
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * Mpq p q) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q _
          ring
        have e2 : ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * Mpq p q) =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * Mpq p q) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          rw [Mpq_symm]
        rw [e1, e2]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        ring
    _ ≤ ∑ p : Mono n d, a p ^ 2 * ((d + 1) / n) := by
        apply Finset.sum_le_sum; intro p _
        by_cases hp : p = default
        · rw [hp, ha0]; simp
        · exact mul_le_mul_of_nonneg_left (Rp_bound hn p hp) (sq_nonneg _)
    _ = ((d : ℝ) + 1) / n * nsq a := by unfold nsq; rw [← Finset.sum_mul]; ring
    _ ≤ cG d / n * nsq a := by
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun p _ => sq_nonneg _)
        exact div_le_div_of_nonneg_right (cG_ge d hd) hnR.le

private lemma glue_inj (n j i : ℕ) (h : 2 * i ≤ j) :
    Function.Injective (fun cw : (Fin i → Fin n) × (Fin (j - 2 * i) → Fin n) => glue j i cw.1 cw.2) := by
  rintro ⟨c, w⟩ ⟨c', w'⟩ hcw
  simp only at hcw
  have hc : c = c' := by
    funext s
    have := congrFun hcw ⟨2 * s.1, by have := s.2; omega⟩
    simp only [glue] at this
    simp only [show 2 * s.1 < 2 * i by omega, ↓reduceDIte] at this
    have e : (⟨2 * s.1 / 2, by have := s.2; omega⟩ : Fin i) = s := by ext; simp
    rwa [e] at this
  have hw : w = w' := by
    funext r
    have := congrFun hcw ⟨r.1 + 2 * i, by have := r.2; omega⟩
    simp only [glue] at this
    simp only [show ¬ (r.1 + 2 * i < 2 * i) by omega, ↓reduceDIte] at this
    have e : (⟨r.1 + 2 * i - 2 * i, by have := r.2; omega⟩ : Fin (j - 2 * i)) = r := by ext; simp
    rwa [e] at this
  rw [hc, hw]

/-- **Lemma Tr** (proved). -/
theorem lemmaTr53 : LemmaTr53 := by
  intro n j i A hij
  unfold frob trL
  calc ∑ w : Fin (j - 2 * i) → Fin n, (∑ c : Fin i → Fin n, A (glue j i c w)) ^ 2
      ≤ ∑ w : Fin (j - 2 * i) → Fin n, (n : ℝ) ^ i * ∑ c : Fin i → Fin n, A (glue j i c w) ^ 2 := by
        apply Finset.sum_le_sum
        intro w _
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin i → Fin n)))
          (f := fun c => A (glue j i c w))
        simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using this
    _ = (n : ℝ) ^ i * ∑ cw : (Fin i → Fin n) × (Fin (j - 2 * i) → Fin n), A (glue j i cw.1 cw.2) ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    _ ≤ (n : ℝ) ^ i * ∑ u : Fin j → Fin n, A u ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        classical
        rw [← Finset.sum_image (f := fun u => A u ^ 2) (g := fun cw : (Fin i → Fin n) × (Fin (j - 2 * i) → Fin n) => glue j i cw.1 cw.2)
          (fun x _ y _ hxy => glue_inj n j i hij hxy)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

end BstLean.Part53
