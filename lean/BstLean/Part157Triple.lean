import BstLean.Part157Net

/-!
# Part 157, item 3 (first half): the three networks as retained data and residual matrices

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-03-composition.tex`, Lemma `t7:p03:regression` ("conditional on the retained
data the residual matrices `G_W`, `G_A` are independent standard Gaussian matrices").

The three networks have the widths of `MM.md` at `r = 2`: `W : ℝ^{2n} → ℝⁿ` (hidden width
`mW n`), `A : ℝⁿ → ℝⁿ` (hidden width `mA n`), `F : ℝⁿ → ℝ` (hidden width `mF n`).

* `Centres n`: the two computed centres. `bW` is a measurable function of `(W₁, W₂)`. `bA` is a
  measurable function of the retained World data `((W₁, W₂), ĉ)` and of `(A₁, A₂)`.
* `ret D θ`: the RETAINED DATA of the triple `θ = (W, A, F)`:
  `(((W₁, W₂), ĉ), (((A₁, A₂), c_A), F))`, `ĉ = W₃ b_W`, `c_A = A₃ b`.
* `rebuild D c (ω_W, ω_A)`: the triple with retained data `c` and residual matrices `ω_W`, `ω_A`:
  `W₃ = ĉ b_Wᵀ/|b_W|² + ω_W P_{b_W^⊥}`, `A₃ = c_A bᵀ/|b|² + ω_A P_{b^⊥}`.
* `noiseC n`: a product of Gaussian measures; `retVal D`: the map from this product to the
  retained data (`ĉ = √(2/m_W)·|b_W|·ξ_W`, `c_A = √(2/m_A)·|b|·ξ_A`).
* **`triple_disint`**: the pair (retained data, triple) has the distribution of
  `(retVal D x, rebuild D (retVal D x) ω)` with `x ~ noiseC n` and `ω = (ω_W, ω_A)` two
  independent Gaussian matrices, independent of `x`.
* `retDist D`: the distribution of the retained data; `noise_retVal`: it is the image of
  `noiseC n` under `retVal D`.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)

/-- The two hidden matrices of `W`. -/
abbrev WHid (n : ℕ) : Type := HidParam (2 * n) (mW n)
/-- The two hidden matrices of `A`. -/
abbrev AHid (n : ℕ) : Type := HidParam n (mA n)
/-- The weights of `F`. -/
abbrev FPar (n : ℕ) : Type := MlpParam n (mF n) 1
/-- The retained data of `W`: `((W₁, W₂), ĉ)`. -/
abbrev WRet (n : ℕ) : Type := WHid n × (Fin n → ℝ)
/-- The retained data of `A`: `((A₁, A₂), c_A)`. -/
abbrev ARet (n : ℕ) : Type := AHid n × (Fin n → ℝ)
/-- **The retained data**: `(((W₁, W₂), ĉ), (((A₁, A₂), c_A), F))`. -/
abbrev Ret (n : ℕ) : Type := WRet n × (ARet n × FPar n)
/-- The three networks `(W, A, F)` with the widths of the Focus, `r = 2`. -/
abbrev Net3 (n : ℕ) : Type := Triple (2 * n) (mW n) n (mA n) (mF n)
/-- A residual matrix of `W₃`. -/
abbrev ResW (n : ℕ) : Type := Matrix (Fin n) (Fin (mW n)) ℝ
/-- A residual matrix of `A₃`. -/
abbrev ResA (n : ℕ) : Type := Matrix (Fin n) (Fin (mA n)) ℝ

/-- **The two computed centres.** `bW (W₁, W₂)` is the centre of the last hidden layer of `W`.
`bA ((W₁, W₂), ĉ) (A₁, A₂)` is the centre of the last hidden layer of `A`. The two maps are
measurable. They read no entry of `W₃` or `A₃` except through `ĉ = W₃ b_W`. -/
structure Centres (n : ℕ) where
  /-- The centre of the last hidden layer of `W`. -/
  bW : WHid n → Fin (mW n) → ℝ
  /-- The centre of the last hidden layer of `A`. -/
  bA : WRet n → AHid n → Fin (mA n) → ℝ
  mbW : Measurable bW
  mbA : Measurable (fun p : WRet n × AHid n => bA p.1 p.2)

variable {n : ℕ}

/-- **The retained data of the triple** `θ = (W, A, F)`. -/
noncomputable def ret (D : Centres n) (θ : Net3 n) : Ret n :=
  (netRet D.bW θ.1, (netRet (D.bA (netRet D.bW θ.1)) θ.2.1, θ.2.2))

/-- **The triple with retained data `c` and residual matrices `ω = (ω_W, ω_A)`.** -/
noncomputable def rebuild (D : Centres n) (c : Ret n) (ω : ResW n × ResA n) : Net3 n :=
  (netOf D.bW c.1.1 c.1.2 ω.1, (netOf (D.bA c.1) c.2.1.1 c.2.1.2 ω.2, c.2.2))

/-- The distribution of a residual matrix of `W₃`: Gaussian entries of variance `2/m_W`. -/
noncomputable def resW (n : ℕ) : Measure (ResW n) := gaussMat n (mW n) (2 / (mW n : ℝ))
/-- The distribution of a residual matrix of `A₃`: Gaussian entries of variance `2/m_A`. -/
noncomputable def resA (n : ℕ) : Measure (ResA n) := gaussMat n (mA n) (2 / (mA n : ℝ))

instance : IsProbabilityMeasure (resW n) := by unfold resW; infer_instance
instance : IsProbabilityMeasure (resA n) := by unfold resA; infer_instance

/-- The noise of the retained World data: `(W₁, W₂)` and a standard Gaussian vector. -/
noncomputable def cWm (n : ℕ) : Measure (WRet n) :=
  (hidGauss (2 * n) (mW n)).prod (stdGauss (Fin n))
/-- The noise of the retained Agent data: `(A₁, A₂)` and a standard Gaussian vector. -/
noncomputable def cAm (n : ℕ) : Measure (ARet n) :=
  (hidGauss n (mA n)).prod (stdGauss (Fin n))

instance : IsProbabilityMeasure (cWm n) := by unfold cWm; infer_instance
instance : IsProbabilityMeasure (cAm n) := by unfold cAm; infer_instance

/-- **The noise space of the retained data**: `(W₁, W₂)`, a standard Gaussian vector `ξ_W`,
`(A₁, A₂)`, a standard Gaussian vector `ξ_A`, and `F`, all independent. -/
noncomputable def noiseC (n : ℕ) : Measure (Ret n) :=
  (cWm n).prod ((cAm n).prod (mlpGauss n (mF n) 1))

instance : IsProbabilityMeasure (noiseC n) := by unfold noiseC; infer_instance

/-- The retained World data from the noise: `ĉ = √(2/m_W)·|b_W|·ξ_W`. -/
noncomputable def retValW (D : Centres n) (x : WRet n) : WRet n :=
  (x.1, cOf (2 / (mW n : ℝ)) (D.bW x.1) x.2)

/-- **The retained data from the noise**: `ĉ = √(2/m_W)·|b_W|·ξ_W`, `c_A = √(2/m_A)·|b|·ξ_A`. -/
noncomputable def retVal (D : Centres n) (x : Ret n) : Ret n :=
  (retValW D x.1,
    ((x.2.1.1, cOf (2 / (mA n : ℝ)) (D.bA (retValW D x.1) x.2.1.1) x.2.1.2), x.2.2))

/-- **The distribution of the retained data** of the three random networks. -/
noncomputable def retDist (D : Centres n) : Measure (Ret n) := (mlpTriple 2 n).map (ret D)

lemma measurable_netRet_comp {α : Type*} [MeasurableSpace α] {k m q : ℕ}
    {b : α → HidParam k m → Fin m → ℝ} (hb : Measurable (fun p : α × HidParam k m => b p.1 p.2))
    {θ : α → MlpParam k m q} (hθ : Measurable θ) :
    Measurable (fun a => netRet (b a) (θ a)) := by
  have hh : Measurable (fun a => (((θ a).1, (θ a).2.1) : HidParam k m)) :=
    (measurable_fst.comp hθ).prodMk (measurable_fst.comp (measurable_snd.comp hθ))
  have hb' : Measurable (fun a => b a ((θ a).1, (θ a).2.1)) := hb.comp (measurable_id.prodMk hh)
  have h2 : Measurable (fun a => (θ a).2.2.mulVec (b a ((θ a).1, (θ a).2.1))) := by
    have := (measurable_mulVec_joint (n := q) (m := m)).comp
      ((measurable_snd.comp (measurable_snd.comp hθ)).prodMk hb')
    exact this
  exact hh.prodMk h2

lemma measurable_ret (D : Centres n) : Measurable (ret D) := by
  have h1 : Measurable (fun θ : Net3 n => netRet D.bW θ.1) :=
    (measurable_netRet D.mbW).comp measurable_fst
  have h2 : Measurable (fun θ : Net3 n => netRet (D.bA (netRet D.bW θ.1)) θ.2.1) :=
    measurable_netRet_comp (b := fun θ : Net3 n => D.bA (netRet D.bW θ.1))
      (D.mbA.comp ((h1.comp measurable_fst).prodMk measurable_snd))
      (measurable_fst.comp measurable_snd)
  exact h1.prodMk (h2.prodMk (measurable_snd.comp measurable_snd))

lemma measurable_retValW (D : Centres n) : Measurable (retValW D) :=
  measurable_fst.prodMk (measurable_cOf_comp _ (D.mbW.comp measurable_fst) measurable_snd)

lemma measurable_retVal (D : Centres n) : Measurable (retVal D) := by
  have h1 : Measurable (fun x : Ret n => retValW D x.1) :=
    (measurable_retValW D).comp measurable_fst
  have hA : Measurable (fun x : Ret n => x.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hb : Measurable (fun x : Ret n => D.bA (retValW D x.1) x.2.1.1) :=
    D.mbA.comp (h1.prodMk hA)
  have hc : Measurable (fun x : Ret n =>
      cOf (2 / (mA n : ℝ)) (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) :=
    measurable_cOf_comp _ hb (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact h1.prodMk ((hA.prodMk hc).prodMk (measurable_snd.comp measurable_snd))

lemma measurable_netOf_comp {α : Type*} [MeasurableSpace α] {k m q : ℕ}
    {b : α → HidParam k m → Fin m → ℝ} (hb : Measurable (fun p : α × HidParam k m => b p.1 p.2))
    {θ : α → HidParam k m} {c : α → Fin q → ℝ} {M : α → Matrix (Fin q) (Fin m) ℝ}
    (hθ : Measurable θ) (hc : Measurable c) (hM : Measurable M) :
    Measurable (fun a => netOf (b a) (θ a) (c a) (M a)) := by
  have hb' : Measurable (fun a => b a (θ a)) := hb.comp (measurable_id.prodMk hθ)
  have hr : Measurable (fun a => reb (b a (θ a)) (c a) (M a)) := measurable_reb_comp hb' hc hM
  exact (measurable_fst.comp hθ).prodMk ((measurable_snd.comp hθ).prodMk hr)

/-- `(c, ω) ↦ rebuild D c ω` is measurable. -/
lemma measurable_rebuild (D : Centres n) :
    Measurable (fun p : Ret n × (ResW n × ResA n) => rebuild D p.1 p.2) := by
  have hW : Measurable (fun p : Ret n × (ResW n × ResA n) =>
      netOf D.bW p.1.1.1 p.1.1.2 p.2.1) :=
    measurable_netOf_comp (b := fun _ : Ret n × (ResW n × ResA n) => D.bW)
      (D.mbW.comp measurable_snd) (measurable_fst.comp (measurable_fst.comp measurable_fst))
      (measurable_snd.comp (measurable_fst.comp measurable_fst))
      (measurable_fst.comp measurable_snd)
  have hA : Measurable (fun p : Ret n × (ResW n × ResA n) =>
      netOf (D.bA p.1.1) p.1.2.1.1 p.1.2.1.2 p.2.2) :=
    measurable_netOf_comp (b := fun p : Ret n × (ResW n × ResA n) => D.bA p.1.1)
      (D.mbA.comp (((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk
        measurable_snd))
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))
      (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))
      (measurable_snd.comp measurable_snd)
  exact hW.prodMk (hA.prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst)))

/-! ## The proof of the decomposition -/

/-- The noise form of `W`: `(W₁, W₂)`, a standard Gaussian vector, a Gaussian matrix. -/
noncomputable def piW (n : ℕ) : Measure (WHid n × ((Fin n → ℝ) × ResW n)) :=
  (hidGauss (2 * n) (mW n)).prod ((stdGauss (Fin n)).prod (resW n))
/-- The noise form of `A`. -/
noncomputable def piA (n : ℕ) : Measure (AHid n × ((Fin n → ℝ) × ResA n)) :=
  (hidGauss n (mA n)).prod ((stdGauss (Fin n)).prod (resA n))

instance : IsProbabilityMeasure (piW n) := by unfold piW; infer_instance
instance : IsProbabilityMeasure (piA n) := by unfold piA; infer_instance

lemma stepW (D : Centres n) :
    (mlpGauss (2 * n) (mW n) n).map (fun W => (netRet D.bW W, W)) =
      (piW n).map (netPsi D.bW) := net_split D.mbW

lemma stepA (D : Centres n) (wc : WRet n) :
    (mlpGauss n (mA n) n).map (fun A => (netRet (D.bA wc) A, A)) =
      (piA n).map (netPsi (D.bA wc)) :=
  net_split (D.mbA.comp measurable_prodMk_left)

/-- The map of step 1 and step 2. -/
noncomputable def psi3 (D : Centres n)
    (p : (WHid n × ((Fin n → ℝ) × ResW n)) × ((AHid n × ((Fin n → ℝ) × ResA n)) × FPar n)) :
    Ret n × Net3 n :=
  (((netPsi D.bW p.1).1, ((netPsi (D.bA (netPsi D.bW p.1).1) p.2.1).1, p.2.2)),
    ((netPsi D.bW p.1).2, ((netPsi (D.bA (netPsi D.bW p.1).1) p.2.1).2, p.2.2)))

/-- Step 1 and step 2: the pair (retained data, triple) as an image of `piW ⊗ (piA ⊗ μ_F)`. -/
lemma triple_step12 (D : Centres n) :
    Measurable (psi3 D) ∧
    (mlpTriple 2 n).map (fun θ => (ret D θ, θ)) =
      ((piW n).prod ((piA n).prod (mlpGauss n (mF n) 1))).map (psi3 D) := by
  -- measurability
  have mΨW : Measurable (netPsi (q := n) D.bW) :=
    measurable_netPsi_comp (b := fun _ : WHid n × ((Fin n → ℝ) × ResW n) => D.bW)
      (D.mbW.comp measurable_snd) measurable_fst (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)
  have mfW : Measurable (fun W : MlpParam (2 * n) (mW n) n => (netRet D.bW W, W)) :=
    (measurable_netRet D.mbW).prodMk measurable_id
  -- step 1
  have a1 : ((mlpGauss (2 * n) (mW n) n).prod
        ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1))).map
        (Prod.map (fun W : MlpParam (2 * n) (mW n) n => (netRet D.bW W, W)) id) =
      ((piW n).prod ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1))).map
        (Prod.map (netPsi D.bW) id) := by
    rw [← Measure.map_prod_map _ _ mfW measurable_id, ← Measure.map_prod_map _ _ mΨW measurable_id,
      stepW D]
  -- the fibre step
  have mwc : Measurable (fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
      (MlpParam n (mA n) n × FPar n) => (netPsi D.bW p.1).1) :=
    measurable_fst.comp (mΨW.comp measurable_fst)
  have mT : Measurable (fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
      (MlpParam n (mA n) n × FPar n) =>
      ((netRet (D.bA (netPsi D.bW p.1).1) p.2.1, p.2.1), p.2.2)) := by
    have h1 : Measurable (fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
        (MlpParam n (mA n) n × FPar n) => netRet (D.bA (netPsi D.bW p.1).1) p.2.1) :=
      measurable_netRet_comp (b := fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
          (MlpParam n (mA n) n × FPar n) => D.bA (netPsi D.bW p.1).1)
        (D.mbA.comp ((mwc.comp measurable_fst).prodMk measurable_snd))
        (measurable_fst.comp measurable_snd)
    exact (h1.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have mwc' : Measurable (fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
      ((AHid n × ((Fin n → ℝ) × ResA n)) × FPar n) => (netPsi D.bW p.1).1) :=
    measurable_fst.comp (mΨW.comp measurable_fst)
  have mS : Measurable (fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
      ((AHid n × ((Fin n → ℝ) × ResA n)) × FPar n) =>
      (netPsi (D.bA (netPsi D.bW p.1).1) p.2.1, p.2.2)) := by
    have h1 : Measurable (fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
        ((AHid n × ((Fin n → ℝ) × ResA n)) × FPar n) =>
        netPsi (D.bA (netPsi D.bW p.1).1) (p.2.1.1, (p.2.1.2.1, p.2.1.2.2))) :=
      measurable_netPsi_comp (b := fun p : (WHid n × ((Fin n → ℝ) × ResW n)) ×
          ((AHid n × ((Fin n → ℝ) × ResA n)) × FPar n) => D.bA (netPsi D.bW p.1).1)
        (D.mbA.comp ((mwc'.comp measurable_fst).prodMk measurable_snd))
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
        (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_snd)))
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd)))
    exact h1.prodMk (measurable_snd.comp measurable_snd)
  have a2 := map_fibre (piW n) ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1))
    ((piA n).prod (mlpGauss n (mF n) 1)) mT mS (fun xW => by
      have mΨA : Measurable (netPsi (q := n) (D.bA (netPsi D.bW xW).1)) :=
        measurable_netPsi_comp
          (b := fun _ : AHid n × ((Fin n → ℝ) × ResA n) => D.bA (netPsi D.bW xW).1)
          ((D.mbA.comp measurable_prodMk_left).comp measurable_snd) measurable_fst
          (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
      have mfA : Measurable (fun A : MlpParam n (mA n) n =>
          (netRet (D.bA (netPsi D.bW xW).1) A, A)) :=
        (measurable_netRet (D.mbA.comp measurable_prodMk_left)).prodMk measurable_id
      have := Measure.map_prod_map (mlpGauss n (mA n) n) (mlpGauss n (mF n) 1) mfA
        (measurable_id (α := FPar n))
      have h2 := Measure.map_prod_map (piA n) (mlpGauss n (mF n) 1) mΨA
        (measurable_id (α := FPar n))
      rw [stepA D (netPsi D.bW xW).1, Measure.map_id] at this
      rw [Measure.map_id] at h2
      exact this.symm.trans h2)
  -- the two outer maps
  have mG1 : Measurable (fun y : (WRet n × MlpParam (2 * n) (mW n) n) ×
      (MlpParam n (mA n) n × FPar n) =>
      (((y.1.1, (netRet (D.bA y.1.1) y.2.1, y.2.2)) : Ret n), ((y.1.2, y.2) : Net3 n))) := by
    have h1 : Measurable (fun y : (WRet n × MlpParam (2 * n) (mW n) n) ×
        (MlpParam n (mA n) n × FPar n) => netRet (D.bA y.1.1) y.2.1) :=
      measurable_netRet_comp (b := fun y : (WRet n × MlpParam (2 * n) (mW n) n) ×
          (MlpParam n (mA n) n × FPar n) => D.bA y.1.1)
        (D.mbA.comp (((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk
          measurable_snd))
        (measurable_fst.comp measurable_snd)
    exact ((measurable_fst.comp measurable_fst).prodMk
      (h1.prodMk (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have mG2 : Measurable (fun z : (WHid n × ((Fin n → ℝ) × ResW n)) ×
      ((ARet n × MlpParam n (mA n) n) × FPar n) =>
      ((((netPsi D.bW z.1).1, (z.2.1.1, z.2.2)) : Ret n),
        (((netPsi D.bW z.1).2, (z.2.1.2, z.2.2)) : Net3 n))) := by
    have hΨ : Measurable (fun z : (WHid n × ((Fin n → ℝ) × ResW n)) ×
        ((ARet n × MlpParam n (mA n) n) × FPar n) => netPsi D.bW z.1) :=
      mΨW.comp measurable_fst
    exact ((measurable_fst.comp hΨ).prodMk
      ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_snd.comp hΨ).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)))
  have b1 := congrArg (Measure.map (fun y : (WRet n × MlpParam (2 * n) (mW n) n) ×
      (MlpParam n (mA n) n × FPar n) =>
      (((y.1.1, (netRet (D.bA y.1.1) y.2.1, y.2.2)) : Ret n), ((y.1.2, y.2) : Net3 n)))) a1
  rw [Measure.map_map mG1 (mfW.prodMap measurable_id),
    Measure.map_map mG1 (mΨW.prodMap measurable_id)] at b1
  have b2 := congrArg (Measure.map (fun z : (WHid n × ((Fin n → ℝ) × ResW n)) ×
      ((ARet n × MlpParam n (mA n) n) × FPar n) =>
      ((((netPsi D.bW z.1).1, (z.2.1.1, z.2.2)) : Ret n),
        (((netPsi D.bW z.1).2, (z.2.1.2, z.2.2)) : Net3 n)))) a2
  rw [Measure.map_map mG2 (measurable_fst.prodMk mT),
    Measure.map_map mG2 (measurable_fst.prodMk mS)] at b2
  exact ⟨mG2.comp (measurable_fst.prodMk mS), b1.trans b2⟩

/-- The rearrangement of the noise coordinates. -/
def shuf (x : Ret n × (ResW n × ResA n)) :
    (WHid n × ((Fin n → ℝ) × ResW n)) × ((AHid n × ((Fin n → ℝ) × ResA n)) × FPar n) :=
  ((x.1.1.1, (x.1.1.2, x.2.1)), ((x.1.2.1.1, (x.1.2.1.2, x.2.2)), x.1.2.2))

lemma measurable_shuf : Measurable (shuf (n := n)) := by
  unfold shuf
  fun_prop

lemma shuf_map :
    ((noiseC n).prod ((resW n).prod (resA n))).map shuf =
      (piW n).prod ((piA n).prod (mlpGauss n (mF n) 1)) := by
  have h4 := prod4_comm (cWm n) ((cAm n).prod (mlpGauss n (mF n) 1)) (resW n) (resA n)
  have hr := prod_right_comm (cAm n) (mlpGauss n (mF n) 1) (resA n)
  have hWa : ((cWm n).prod (resW n)).map MeasurableEquiv.prodAssoc = piW n := by
    unfold cWm piW
    rw [Measure.prodAssoc_prod]
  have hAa : ((cAm n).prod (resA n)).map MeasurableEquiv.prodAssoc = piA n := by
    unfold cAm piA
    rw [Measure.prodAssoc_prod]
  have mrc : Measurable (fun p : (ARet n × FPar n) × ResA n => ((p.1.1, p.2), p.1.2)) := by
    fun_prop
  have mas : Measurable (Prod.map (MeasurableEquiv.prodAssoc :
      (AHid n × (Fin n → ℝ)) × ResA n ≃ᵐ AHid n × ((Fin n → ℝ) × ResA n)) (id : FPar n → FPar n)) :=
    MeasurableEquiv.prodAssoc.measurable.prodMap measurable_id
  have i1 := Measure.map_prod_map ((cAm n).prod (resA n)) (mlpGauss n (mF n) 1)
    (MeasurableEquiv.prodAssoc :
      (AHid n × (Fin n → ℝ)) × ResA n ≃ᵐ AHid n × ((Fin n → ℝ) × ResA n)).measurable
    (measurable_id (α := FPar n))
  rw [Measure.map_id, hAa, ← hr, Measure.map_map mas mrc] at i1
  have msh : Measurable (fun p : (WRet n × (ARet n × FPar n)) × (ResW n × ResA n) =>
      ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by fun_prop
  have i2 := Measure.map_prod_map ((cWm n).prod (resW n))
    (((cAm n).prod (mlpGauss n (mF n) 1)).prod (resA n))
    (MeasurableEquiv.prodAssoc :
      (WHid n × (Fin n → ℝ)) × ResW n ≃ᵐ WHid n × ((Fin n → ℝ) × ResW n)).measurable
    (mas.comp mrc)
  rw [hWa, ← i1, ← h4, Measure.map_map (MeasurableEquiv.prodAssoc.measurable.prodMap
    (mas.comp mrc)) msh] at i2
  rw [i2]
  rfl

/-- **The three random networks as retained data and two residual Gaussian matrices.** The
pair (retained data `ret D θ`, triple `θ`) has the distribution of
`(retVal D x, rebuild D (retVal D x) ω)`, where `x ~ noiseC n` and `ω = (ω_W, ω_A)` are
independent, and `ω_W`, `ω_A` are independent Gaussian matrices with entry variances `2/m_W` and
`2/m_A`. So, conditional on the retained data, the residual matrices are independent Gaussian
matrices, and their distribution does not depend on the retained data. This holds for every pair
of measurable centres, also where a centre is `0`. -/
theorem triple_disint (D : Centres n) :
    (mlpTriple 2 n).map (fun θ => (ret D θ, θ)) =
      ((noiseC n).prod ((resW n).prod (resA n))).map
        (fun x => (retVal D x.1, rebuild D (retVal D x.1) x.2)) := by
  obtain ⟨mΨ, h⟩ := triple_step12 D
  rw [h, ← shuf_map, Measure.map_map mΨ measurable_shuf]
  rfl

/-- The distribution of the retained data is the image of the noise under `retVal D`. -/
theorem noise_retVal (D : Centres n) : (noiseC n).map (retVal D) = retDist D := by
  have h := congrArg (Measure.map Prod.fst) (triple_disint D)
  have mL : Measurable (fun θ : Net3 n => (ret D θ, θ)) := (measurable_ret D).prodMk measurable_id
  have mΦ : Measurable (fun x : Ret n × (ResW n × ResA n) =>
      (retVal D x.1, rebuild D (retVal D x.1) x.2)) :=
    ((measurable_retVal D).comp measurable_fst).prodMk
      ((measurable_rebuild D).comp
        (((measurable_retVal D).comp measurable_fst).prodMk measurable_snd))
  rw [Measure.map_map measurable_fst mL, Measure.map_map measurable_fst mΦ] at h
  have e : (Prod.fst ∘ fun x : Ret n × (ResW n × ResA n) =>
      (retVal D x.1, rebuild D (retVal D x.1) x.2)) = retVal D ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map (measurable_retVal D) measurable_fst, Measure.map_fst_prod] at h
  simp only [measure_univ, one_smul] at h
  exact h.symm

instance (D : Centres n) : IsProbabilityMeasure (retDist D) := by
  have h : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  unfold retDist
  exact (Measure.isProbabilityMeasure_map_iff (measurable_ret D).aemeasurable).2 h

end BstLean.Part157

open BstLean.Part157 in
#print axioms triple_disint
open BstLean.Part157 in
#print axioms noise_retVal
