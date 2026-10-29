import BstLean.Part53Defs

namespace BstLean.Part53.FloorHeat

open MeasureTheory
open BstLean.Part41 (trL glue Tens frob)


/-! Trace composition for the finite heat semigroup. -/

private lemma p4_append_val {ι : Type*} {l i : ℕ} (c : Fin l → ι) (c' : Fin i → ι)
    (u : Fin (l + i)) :
    Fin.append c c' u = if h : u.1 < l then c ⟨u.1, h⟩ else c' ⟨u.1 - l, by omega⟩ := by
  split_ifs with h
  · have : u = Fin.castAdd i ⟨u.1, h⟩ := Fin.ext rfl
    exact (congrArg (Fin.append c c') this).trans (Fin.append_left c c' _)
  · have : u = Fin.natAdd l ⟨u.1 - l, by omega⟩ := Fin.ext (by simp; omega)
    exact (congrArg (Fin.append c c') this).trans (Fin.append_right c c' _)

private lemma p4_glue_glue {ι : Type*} (j l i : ℕ) (hj : 2 * (l + i) ≤ j)
    (c : Fin l → ι) (c' : Fin i → ι) (w : Fin (j - 2 * l - 2 * i) → ι) :
    glue j l c (glue (j - 2 * l) i c' w) =
      glue j (l + i) (Fin.append c c') (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  funext t
  unfold glue
  simp only [p4_append_val]
  split_ifs <;> first
    | rfl
    | (congr 1; apply Fin.ext; simp only; omega)
    | omega

private lemma p4_trL_trL {ι R : Type*} [Fintype ι] [AddCommMonoid R] {j : ℕ} (l i : ℕ)
    (hj : 2 * (l + i) ≤ j) (A : (Fin j → ι) → R) (w : Fin (j - 2 * l - 2 * i) → ι) :
    trL i (trL l A) w = trL (l + i) A (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  classical
  unfold trL
  rw [Finset.sum_comm]
  simp_rw [p4_glue_glue j l i hj]
  rw [← (Fin.appendEquiv l i).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The factorial denominators satisfy the finite exponential convolution identity. -/
lemma factorial_convolution (r : ℕ) (v w : ℝ) :
    (∑ i ∈ Finset.range (r + 1), v ^ i / (i.factorial : ℝ) *
      (w ^ (r - i) / ((r - i).factorial : ℝ))) = (v + w) ^ r / (r.factorial : ℝ) := by
  rw [add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
  have hc : (r.choose i : ℝ) = (r.factorial : ℝ) /
      ((i.factorial : ℝ) * ((r - i).factorial : ℝ)) := by
    apply (eq_div_iff (by positivity)).mpr
    have hh := Nat.choose_mul_factorial_mul_factorial hir
    have hhR : (r.choose i : ℝ) * (i.factorial : ℝ) * ((r - i).factorial : ℝ) =
        (r.factorial : ℝ) := by exact_mod_cast hh
    simpa only [mul_assoc] using hhR
  rw [hc]
  have hi0 : (i.factorial : ℝ) ≠ 0 := by positivity
  have hr0 : (r.factorial : ℝ) ≠ 0 := by positivity
  have hri0 : ((r - i).factorial : ℝ) ≠ 0 := by positivity
  field_simp

noncomputable def heatWeight (c i : ℕ) (v : ℝ) : ℝ :=
  (v / 2) ^ i / (i.factorial : ℝ) * (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ))

/-- The scalar coefficients of successive heat steps compose by addition. -/
lemma heatWeight_convolution (c r : ℕ) (v w : ℝ) :
    (∑ i ∈ Finset.range (r + 1), heatWeight c i v * heatWeight (c + 2 * i) (r - i) w) =
      heatWeight c r (v + w) := by
  have he (i : ℕ) (hi : i ∈ Finset.range (r + 1)) :
      heatWeight c i v * heatWeight (c + 2 * i) (r - i) w =
        ((v / 2) ^ i / (i.factorial : ℝ) * ((w / 2) ^ (r - i) / ((r - i).factorial : ℝ))) *
          (((c + 2 * r).factorial : ℝ) / (c.factorial : ℝ)) := by
    have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
    have hidx : c + 2 * i + 2 * (r - i) = c + 2 * r := by omega
    unfold heatWeight
    rw [hidx]
    have hi0 : (i.factorial : ℝ) ≠ 0 := by positivity
    have hri0 : ((r - i).factorial : ℝ) ≠ 0 := by positivity
    have hc0 : (c.factorial : ℝ) ≠ 0 := by positivity
    have hci0 : ((c + 2 * i).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl he, ← Finset.sum_mul, factorial_convolution]
  unfold heatWeight
  rw [show v / 2 + w / 2 = (v + w) / 2 by ring]

private lemma trace_cast {a b n : ℕ} (h : a = b) (i : ℕ)
    (A : (Fin a → Fin n) → ℝ) (w : Fin (b - 2 * i) → Fin n) :
    trL i (fun z : Fin b → Fin n => A (fun t => z ⟨t.1, by omega⟩)) w =
      trL i A (fun t => w ⟨t.1, by omega⟩) := by
  subst b
  rfl

noncomputable def traceFamily {n : ℕ} (i : ℕ) (A : Tens n) : Tens n := fun c w =>
  trL i (A (c + 2 * i)) (fun t => w ⟨t.1, by have := t.2; omega⟩)

private lemma trace_order_cast {n a b r c : ℕ} (h : a = b) (ha : a - 2 * r ≤ c)
    (A : Tens n) (w : Fin c → Fin n) :
    trL r (A a) (fun t => w ⟨t.1, by have := t.2; omega⟩) =
      trL r (A b) (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  subst b
  rfl

/-- Traces on tensor families compose without a dimension-dependent loss. -/
lemma traceFamily_comp {n : ℕ} (i j : ℕ) (A : Tens n) :
    traceFamily i (traceFamily j A) = traceFamily (i + j) A := by
  funext c w
  unfold traceFamily
  have hc : (c + 2 * i + 2 * j) - 2 * j = c + 2 * i := by omega
  rw [trace_cast hc i]
  have hj : 2 * (j + i) ≤ c + 2 * i + 2 * j := by omega
  rw [p4_trL_trL j i hj]
  change trL (j + i) (A (c + 2 * i + 2 * j)) (fun t => w ⟨t.1, by have := t.2; omega⟩) = _
  exact (trace_order_cast (r := j + i) (by omega : c + 2 * i + 2 * j = c + 2 * (j + i))
    (by omega) A w).trans
      (congrArg (fun r => traceFamily r A c w) (Nat.add_comm j i))

lemma heat_reindex (c k : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => c + 2 * i + 2 * j ≤ k), F i j) =
    ∑ r ∈ (Finset.range (k + 1)).filter (fun r => c + 2 * r ≤ k),
      ∑ i ∈ Finset.range (r + 1), F i (r - i) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun (p : Σ _ : ℕ, ℕ) _ => (⟨p.1 + p.2, p.1⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at *
    omega
  · intro p hp q hq he
    have h1 := congrArg Sigma.fst he
    have h2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) he
    cases p
    cases q
    dsimp only at h1 h2
    congr 1; omega
  · intro p hp
    refine ⟨⟨p.2, p.1 - p.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at *
      omega
    · have hp' := hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hp'
      apply Sigma.ext (by dsimp only; omega)
      rfl
  · intro p hp
    change F p.1 p.2 = F p.1 (p.1 + p.2 - p.1)
    simp

private lemma trace_sum {ι κ : Type*} [Fintype ι] {j : ℕ} (l : ℕ) (S : Finset κ)
    (b : κ → ℝ) (A : κ → (Fin j → ι) → ℝ) :
    trL l (fun w => ∑ x ∈ S, b x * A x w) = fun w => ∑ x ∈ S, b x * trL l (A x) w := by
  funext w
  simp only [trL, Finset.mul_sum]
  exact Finset.sum_comm

lemma traceFamily_heat {n : ℕ} (k c i : ℕ) (v : ℝ) (A : Tens n)
    (w : Fin c → Fin n) :
    traceFamily i (heatA k v A) c w =
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => c + 2 * i + 2 * j ≤ k),
        heatWeight (c + 2 * i) j v * traceFamily (i + j) A c w := by
  classical
  unfold traceFamily heatA
  rw [trace_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change heatWeight (c + 2 * i) j v * traceFamily i (traceFamily j A) c w = _
  rw [traceFamily_comp]
  rfl

lemma heatA_add {n : ℕ} (k c : ℕ) (v w : ℝ) (A : Tens n)
    : heatA k v (heatA k w A) c = heatA k (v + w) A c := by
  classical
  funext z
  change (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
    heatWeight c i v * traceFamily i (heatA k w A) c z) = _
  simp_rw [traceFamily_heat, Finset.mul_sum, ← mul_assoc]
  rw [heat_reindex]
  change (∑ r ∈ (Finset.range (k + 1)).filter (fun r => c + 2 * r ≤ k),
    ∑ i ∈ Finset.range (r + 1),
      heatWeight c i v * heatWeight (c + 2 * i) (r - i) w *
        traceFamily (i + (r - i)) A c z) = _
  change _ = ∑ r ∈ (Finset.range (k + 1)).filter (fun r => c + 2 * r ≤ k),
    heatWeight c r (v + w) * traceFamily r A c z
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = ∑ i ∈ Finset.range (r + 1),
        heatWeight c i v * heatWeight (c + 2 * i) (r - i) w * traceFamily r A c z := by
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
      rw [Nat.add_sub_of_le hir]
    _ = _ := by rw [← Finset.sum_mul, heatWeight_convolution]

lemma traceFamily_zero {n : ℕ} (A : Tens n) : traceFamily 0 A = A := by
  funext c w
  unfold traceFamily
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

lemma heatA_correction {n : ℕ} (k c : ℕ) (v : ℝ) (A : Tens n) (hc : c ≤ k)
    (w : Fin c → Fin n) :
    heatA k v A c w - A c w =
      ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
        heatWeight c i v * traceFamily i A c w := by
  classical
  have h0 : 0 ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k) := by simp [hc]
  have hs := Finset.sum_erase_add
    ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k))
    (fun i => heatWeight c i v * traceFamily i A c w) h0
  have hz : heatWeight c 0 v * traceFamily 0 A c w = A c w := by
    rw [traceFamily_zero]
    simp [heatWeight, Nat.factorial_ne_zero]
  change (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
    heatWeight c i v * traceFamily i A c w) - A c w = _
  rw [← hs, hz]
  ring

lemma heatA_shift {n : ℕ} (k c : ℕ) (v w : ℝ) (A : Tens n) :
    heatA k (v - w) (heatA k w A) c = heatA k v A c := by
  rw [heatA_add, sub_add_cancel]

lemma traceFamily_frob {n : ℕ} (c i : ℕ) (A : Tens n) :
    frob (traceFamily i A c) = frob (trL i (A (c + 2 * i))) := by
  classical
  let e : (Fin c → Fin n) ≃ (Fin (c + 2 * i - 2 * i) → Fin n) :=
    Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _)
  exact e.sum_comp (fun w => trL i (A (c + 2 * i)) w ^ 2)

lemma heatA_correction_frob {n : ℕ} (k c : ℕ) (v : ℝ) (A : Tens n)
    (hc : c ≤ k) (hTr : LemmaTr53) :
    frob (fun w => heatA k v A c w - A c w) ≤
      (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          heatWeight c i v ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i)) := by
  classical
  let S := ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0
  have hcard : (S.card : ℝ) ≤ k + 1 := by
    have hh : S.card ≤ (Finset.range (k + 1)).card :=
      Finset.card_le_card ((Finset.erase_subset 0 _).trans (Finset.filter_subset _ _))
    simpa using (Nat.cast_le (α := ℝ)).mpr hh
  have hsq (z : Fin c → Fin n) :
      (heatA k v A c z - A c z) ^ 2 ≤
        (k + 1 : ℝ) * ∑ i ∈ S, (heatWeight c i v * traceFamily i A c z) ^ 2 := by
    rw [heatA_correction k c v A hc]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
      (fun i => heatWeight c i v * traceFamily i A c z)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ z : Fin c → Fin n,
        (k + 1 : ℝ) * ∑ i ∈ S, (heatWeight c i v * traceFamily i A c z) ^ 2 :=
      Finset.sum_le_sum (fun z _ => hsq z)
    _ = (k + 1 : ℝ) * ∑ i ∈ S, heatWeight c i v ^ 2 * frob (traceFamily i A c) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [mul_pow, ← Finset.mul_sum]
      rfl
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      rw [traceFamily_frob]
      have hh := hTr n (c + 2 * i) i (A (c + 2 * i)) (by omega)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg (heatWeight c i v))

end BstLean.Part53.FloorHeat
