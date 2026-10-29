import BstLean.Part293EndpointInterface
import BstLean.Part236World
import BstLean.Part289Root
import BstLean.Part253Exp

/-! Design-parametric RF assembly for the low-floor program. No old-program equality is used. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part156 BstLean.Part157 BstLean.Part159
open BstLean.Part203 BstLean.Part232 BstLean.Part236 BstLean.Part289

structure WorldInputs (n : ℕ) (E : Set (Ret n)) where
  x : Ret n → ℝ
  y : Ret n → ℝ
  x_nonneg : ∀ z, 0 ≤ x z
  y_nonneg : ∀ z, 0 ≤ y z
  maximum : ∀ z ∈ E, x z + y z ≤ frameMaximum
  radius_integrable : IntegrableOn (fun z => HbarW (statedDesign2 n) z ^ 2)
    E (retDist (statedDesign2 n).toCentres)
  radius_moment : ∫ z in E, HbarW (statedDesign2 n) z ^ 2
    ∂retDist (statedDesign2 n).toCentres ≤ radiusMoment
  x_integrable : IntegrableOn (fun z => x z ^ 2) E (retDist (statedDesign2 n).toCentres)
  y_integrable : IntegrableOn y E (retDist (statedDesign2 n).toCentres)
  x_moment : ∫ z in E, x z ^ 2 ∂retDist (statedDesign2 n).toCentres ≤ 0.372 * coeffK ^ 2
  y_moment : ∫ z in E, y z ∂retDist (statedDesign2 n).toCentres ≤ 0.448 * coeffD
  frame : ∀ z ∈ E, FRAME_W_hyp (statedDesign2 n).toCentres
    ((worldBase + x z + y z) / n) {z}

structure RowInputs (n : ℕ) (t : ℝ) where
  event : NetworkCharge (retDist (statedDesign2 n).toCentres) retainedCharge
  world : WorldInputs n event.event
  agent : FRAME_A_hyp (statedDesign2 n) (agentFrame / n) event.event
  root : RootPrice event.event (QStand (statedDesign2 n) t)
    (qTilde (statedDesign2 n) t) rootAllowance

def productCell {n : ℕ} {E : Set (Ret n)} (W : WorldInputs n E)
    (C : EndpointInputs) (i j : ℕ) : Set (Ret n) :=
  E ∩ {z | radiusCell C.radius.h i (HbarW (statedDesign2 n) z) ∧
    radiusCell C.frame.h j (W.x z + W.y z)}

theorem WorldInputs.cell_frame {n : ℕ} (hn : 0 < n) {E : Set (Ret n)}
    (W : WorldInputs n E) (C : EndpointInputs) (i j : ℕ) :
    FRAME_W_hyp (statedDesign2 n).toCentres ((worldBase + C.frame.h (j + 1)) / n)
      (productCell W C i j) := by
  intro z hz w
  have h := W.frame z hz.1 z (by rfl) w
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hh := hz.2.2.2
  linarith

theorem sampling_payment : 2 * exp (-((10 ^ 12 : ℕ) : ℝ) * samplingDeviation ^ 2) ≤
    samplingCharge := by
  have h := BstLean.Part253.exp_negative_bound 25
    (by norm_num : ((2.71828 : ℝ) ^ 25)⁻¹ ≤ 1 / (2 * 10 ^ 9))
  norm_num [samplingDeviation, samplingCharge] at h ⊢
  linarith

theorem classifier_of_row {n : ℕ} (hn : 8000 ≤ n) (t : ℝ)
    (C : EndpointInputs) (R : RowInputs n t) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {z | successNet z.1 t (progOut (statedDesign2 n) t aL (10 ^ 12) z.1 z.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqt : Measurable (qTilde (statedDesign2 n) t) :=
    (measurable_hitFn (statedDesign2 n) t).stronglyMeasurable.integral_prod_right'.measurable
  have hf := rf_end_master (retDist (statedDesign2 n).toCentres)
    ((resW n).prod (resA n)) (sampMeas (10 ^ 12) n) R.event.measurable C.radius C.frame
    (ρ := HbarW (statedDesign2 n)) (x := R.world.x) (y := R.world.y)
    (Q := QStand (statedDesign2 n) t) (qt := qTilde (statedDesign2 n) t)
    (fun _ => sqrt_nonneg _) R.world.x_nonneg R.world.y_nonneg
    (fun z hz => by rw [C.maximum]; exact R.world.maximum z hz) hqt
    (measurable_pRes (statedDesign2 n).toCentres t)
    (fun _ => pRes_nonneg _ _ _ _) (fun _ => pRes_le_one hn1 _ _ _ _)
    (measurable_hitFrac (statedDesign2 n) t (10 ^ 12))
    (fun z => by
      unfold hitFrac
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Finset.sum_nonneg
      intro i _
      rcases hits_01 (statedDesign2 n) t (10 ^ 12) i z with h | h
      · exact le_of_eq h.symm
      · exact (by norm_num : (0 : ℝ) ≤ 1).trans_eq h.symm)
    hnR (by norm_num [worldBase]) (by norm_num [agentFrame])
    (by norm_num [aL]) (by norm_num [rootAllowance])
    (by norm_num [samplingDeviation]) (by norm_num [endpointIntercept])
    (by norm_num [radiusPrice]) (by norm_num [quadraticPrice])
    (by norm_num [linearPrice]) (by norm_num [samplingCharge])
    (C.atDimension n) R.world.radius_integrable R.world.x_integrable R.world.y_integrable
    R.world.radius_moment R.world.x_moment R.world.y_moment
    (C.payment_atDimension hn) C.terminal
    (fun z _ => QStand_mem_01 _ _ z) R.root.bound
    (fun z hz i hi j hj hr hs _ => by
      have hc : 0 < worldBase + C.frame.h (j + 1) :=
        add_pos_of_pos_of_nonneg (by norm_num [worldBase])
          (C.frame.toRadiusCover.nonneg (by omega))
      apply network_free_cpr hn1 (statedDesign2 n) t hc
        (by norm_num [agentFrame]) (C.radius.nonneg (by omega))
        (R.world.cell_frame (by omega) C i j)
        (fun z hz => R.agent z hz.1) _ z ⟨hz, hr, hs⟩
      intro z hz ω hT
      exact (replw_hellinger hn1 (statedDesign2 n) z hT).trans hz.2.1.2)
    (fun z _ => (draw_root_charge (statedDesign2 n) t (10 ^ 12) z
      (by norm_num [samplingDeviation])).trans sampling_payment)
    R.event.complement
  have hb : _ ≤ ledger := hf.trans (by
    unfold ledger restrictedPayment
    norm_num [endpointIntercept, radiusPrice, radiusMoment, quadraticPrice, linearPrice,
      coeffK, coeffD, samplingCharge] <;> linarith)
  exact (show (99 / 100 : ℝ) ≤ 1 - ledger by linarith [ledger_le_one_percent]).trans
    (classifier_of_retained_lm (statedDesign2 n) t aL (10 ^ 12) hb)

structure BandInputs where
  endpoint : EndpointInputs
  rows : ∀ n ∈ Icc (8000 : ℕ) 11882, ∀ t : ℝ, RowInputs n t

theorem classifier_stated2_8000_11882_of_supplies (B : BandInputs) :
    ∀ n ∈ Icc (8000 : ℕ) 11882, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {z | successNet z.1 t (progOut (statedDesign2 n) t aL (10 ^ 12) z.1 z.2)} :=
  fun n hn t => classifier_of_row hn.1 t B.endpoint (B.rows n hn t)

end BstLean.Part293

/-- info: 'BstLean.Part293.classifier_stated2_8000_11882_of_supplies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000_11882_of_supplies
