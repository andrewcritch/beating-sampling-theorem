import BstLean.Part172Adm

/-!
# Part 172 (file `AMeas`): measurability of the first-layer directions in `A₁`

No proof is left open; no `native_decide` or `axiom` is used.

* `fr_meas_e1`, `fr_meas_e2`: `A ↦ e₁(mkR wr (A, 0))`, `A ↦ e₂(mkR wr (A, 0), g)` are measurable.
* `fr_meas_cdir`: `(A, y) ↦ ĉ'(mkR wr (A, 0), s, y)` is measurable, for every latitude `s`.
-/

namespace BstLean.Part172

open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part157
open BstLean.Part169 (a1Bar nodeS)
open BstLean.Part170 (mkR hB tA)
open BstLean.Part171 (e1v e2v)
open BstLean.Part167 (perp)
open BstLean.Part134 (res lam)

variable {n : ℕ}

lemma fr_meas_mk (wr : WRet n) :
    Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => mkR wr (A, 0)) :=
  BstLean.Part170.measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))

lemma fr_meas_qvec {m : ℕ} (t : ℝ) :
    Measurable (fun h : Fin m → ℝ => ((normSq h)⁻¹ * (√t * √(normSq h))) • h) := by
  have h1 : Measurable (fun h : Fin m → ℝ => normSq h) := continuous_normSq.measurable
  exact ((h1.inv).mul (measurable_const.mul h1.sqrt)).smul measurable_id

lemma fr_meas_res {m : ℕ} : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => res p.1 p.2) := by
  unfold res lam
  have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => normSq p.1) :=
    continuous_normSq.measurable.comp measurable_fst
  have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ∑ j, p.2 j * p.1 j) := by fun_prop
  exact measurable_snd.sub ((h2.div h1).smul measurable_fst)

lemma fr_meas_perp {m : ℕ} : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => perp p.1 p.2) := by
  unfold perp
  have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => normSq p.1) :=
    continuous_normSq.measurable.comp measurable_fst
  have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ∑ j, p.2 j * p.1 j) := by fun_prop
  exact measurable_snd.sub (((h1.inv).mul h2).smul measurable_fst)

lemma fr_meas_e1 (wr : WRet n) :
    Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => e1v (mkR wr (A, 0))) := by
  unfold e1v
  exact (fr_meas_qvec _).comp (BstLean.Part171.measurable_hB.comp (fr_meas_mk wr))

lemma fr_meas_e2 (wr : WRet n) (g : ℕ) :
    Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => e2v (mkR wr (A, 0)) g) := by
  unfold e2v
  have hh := BstLean.Part171.measurable_hB.comp (fr_meas_mk (n := n) wr)
  have ha := (BstLean.Part171.measurable_a1Bar_node (n := n) g).comp (fr_meas_mk wr)
  exact (fr_meas_qvec _).comp (fr_meas_res.comp (hh.prodMk ha))

lemma fr_meas_cdir (wr : WRet n) (s : ℝ) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
      cdirP (mkR wr (p.1, 0)) s p.2) := by
  unfold cdirP
  have hh : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
      hB (mkR wr (p.1, 0))) :=
    (BstLean.Part171.measurable_hB.comp (fr_meas_mk (n := n) wr)).comp measurable_fst
  have ha : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
      a1Bar (mkR wr (p.1, 0)) s) :=
    measurable_pi_iff.mpr fun i => BstLean.Part169.measurable_a1Bar_comp
      ((fr_meas_mk wr).comp measurable_fst) measurable_const i
  have hr := fr_meas_res.comp (hh.prodMk ha)
  have hP := fr_meas_perp.comp (hr.prodMk (fr_meas_perp.comp (hh.prodMk measurable_snd)))
  exact ((continuous_normSq.measurable.comp hP).sqrt.inv).smul hP

end BstLean.Part172
