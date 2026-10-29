import BstLean.Part142Persp

/-!
# Part 142: the statements of the one-layer links of the distance form

Role: `delegations/statements/p142-spec.md`, item 2. This file has STATEMENTS only (as
propositions): the files `Part142ReluD` and `Part142LinD` prove them, and the files of the
whole-network links use them as hypotheses. Notation: `Φ_G = phiD G`, `e = eD` (`|y − y′|²/2`),
`δ = dlt` (`(|y| − |y′|)²/2`), `b_G = bG G`, `K₄(m) = K4 m` (Part 133), `K_r(m) = Kr m`.

For a Gaussian matrix `M` with `m` rows and entry variance `v`, and fixed `h, h′`:

* `ReluEDStmt`: `‖e(ReLU(Mh), ReLU(Mh′)) − (m/2)v·Φ_κ(h, h′)‖₂ ≤ (√3/2)√m·v·|h − h′|²`.
* `ReluDltStmt`: `‖δ(ReLU(Mh), ReLU(Mh′)) − (m/2)v·δ(h, h′)‖₂ ≤
    (m/2)v·((4K_r/m)(|h|² + |h′|²) + (√5/√m)·||h|² − |h′|²|)`.
* `ReluPhiStmt`: `‖Φ_G(ReLU(Mh), ReLU(Mh′)) − (m/2)v·Φ_{G∘κ}(h, h′)‖₂ ≤ (m/2)v·((√3/√m)|h − h′|² +
    b_G(√5/(2√m))(|h|² + |h′|²) + G(0)·((4K_r/m)(|h|² + |h′|²) + (√5/√m)||h|² − |h′|²| + 2δ(h, h′)))`.
* `LinEDStmt`, `LinDltStmt`, `LinPhiStmt`: the same for `Mh`, `Mh′` (no ReLU), scale `m·v`,
  with `1/√(2m)`, `K₄(m)/m`, `√2/√m`; `LinPhiStmt` needs `⟨h, h′⟩ ≥ 0`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

/-- `K_r(m) = √(75/16 + 35/m)`: `E(|ReLU(Mh)|² − (m/2)v|h|²)⁴ ≤ (m·K_r(m))²·(v|h|²)⁴`. -/
noncomputable def Kr (m : ℕ) : ℝ := √(75 / 16 + 35 / (m : ℝ))

lemma Kr_nonneg (m : ℕ) : 0 ≤ Kr m := Real.sqrt_nonneg _

def ReluSqStmt : Prop :=
  ∀ {m k : ℕ} {v : ℝ}, 0 < v → 1 ≤ m → ∀ h : Fin k → ℝ,
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * (v * normSq h))
      (√5 / 2 * √(m : ℝ) * (v * normSq h)) ∧
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * (v * normSq h)) ^ 2)
      ((m : ℝ) * Kr m * (v * normSq h) ^ 2)

def ReluEDStmt : Prop :=
  ∀ {m k : ℕ} {v : ℝ}, 0 < v → 1 ≤ m → ∀ h h' : Fin k → ℝ,
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        eD (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * v * phiD kappa h h')
      (√3 / 2 * √(m : ℝ) * v * normSq (h - h'))

def ReluDltStmt : Prop :=
  ∀ {m k : ℕ} {v : ℝ}, 0 < v → 1 ≤ m → ∀ h h' : Fin k → ℝ,
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dlt (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * v * dlt h h')
      ((m : ℝ) / 2 * v * (4 * Kr m / (m : ℝ) * (normSq h + normSq h') +
        √5 / √(m : ℝ) * |normSq h - normSq h'|))

def ReluPhiStmt : Prop :=
  ∀ {m k : ℕ} {G : ℝ → ℝ}, KGood G → ∀ {v : ℝ}, 0 < v → 1 ≤ m → ∀ h h' : Fin k → ℝ,
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (reluV (M.mulVec h)) (reluV (M.mulVec h')) -
          (m : ℝ) / 2 * v * phiD (G ∘ kappa) h h')
      ((m : ℝ) / 2 * v * (√3 / √(m : ℝ) * normSq (h - h') +
        bG G * (√5 / (2 * √(m : ℝ))) * (normSq h + normSq h') +
        G 0 * (4 * Kr m / (m : ℝ) * (normSq h + normSq h') +
          √5 / √(m : ℝ) * |normSq h - normSq h'| + 2 * dlt h h')))

def LinEDStmt : Prop :=
  ∀ {m k : ℕ} {v : ℝ}, 0 < v → 1 ≤ m → ∀ h h' : Fin k → ℝ,
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        eD (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * eD h h')
      (√(m : ℝ) / √2 * v * normSq (h - h'))

def LinDltStmt : Prop :=
  ∀ {m k : ℕ} {v : ℝ}, 0 < v → 1 ≤ m → ∀ h h' : Fin k → ℝ,
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dlt (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * dlt h h')
      ((m : ℝ) * v * (K4 m / (m : ℝ) * (normSq h + normSq h') +
        √2 / √(m : ℝ) * |normSq h - normSq h'|))

def LinPhiStmt : Prop :=
  ∀ {m k : ℕ} {G : ℝ → ℝ}, KGood G → ∀ {v : ℝ}, 0 < v → 1 ≤ m → ∀ h h' : Fin k → ℝ,
    0 ≤ dotp h h' →
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * phiD G h h')
      ((m : ℝ) * v * (normSq (h - h') / √(2 * (m : ℝ)) +
        bG G * (normSq h + normSq h') / √(2 * (m : ℝ)) +
        G 0 * (K4 m / (m : ℝ) * (normSq h + normSq h') +
          √2 / √(m : ℝ) * |normSq h - normSq h'| + 2 * dlt h h')))

end BstLean.Part142
