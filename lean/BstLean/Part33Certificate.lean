import Mathlib

/-!
# Part 33 (cubic `(3,2)`), the arithmetic certificate, at every `n ≥ 6000`

`proofs/option-m/33-explicit-32-orthogonal.tex`, proved-tools version (no `Y₅` tail), at `δ = 1/2`, `c₀ = 2`, with the free
parameters fixed as in `delegations/answers/p33-cert-spec-opus.md` §2: `θ = 19/20`, `δ_o = 6/25` (branches H, U), `θ_G = 1/2`.
This file proves, for every `n = 6000 + t`, the per-quantity bounds A1–A15 and the window closures Bi, Bii, Biii of that
specification, and the quadratic certificate that turns them into accuracy. It does not prove that the closed forms are the
right costs, moments and failure bounds (the analogue of part 29's layers L2–L4).
-/

namespace BstLean.Part33

/-! ## Closed forms (specification §1) -/

noncomputable def D (n : ℝ) : ℝ := n * (n + 1) * (n + 2) / 2
noncomputable def kappa4 (n : ℝ) : ℝ := (n - 1) * (n - 2) * (n - 3) / ((n + 2) * (n + 4) * (n + 6))
noncomputable def kappa6 (n : ℝ) : ℝ :=
  (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / ((n + 2) * (n + 4) * (n + 6) * (n + 8) * (n + 10))
noncomputable def P (n : ℝ) : ℝ := n ^ 2 * (n + 3) / 2
noncomputable def CE (n : ℝ) : ℝ := 3 / 2 * n ^ 5 + 5 * n ^ 4
noncomputable def CG (n : ℝ) : ℝ := 7 / 2 * n ^ 4 + 8 * n ^ 3
noncomputable def CH (n : ℝ) : ℝ := n * (n + 1) * (2 * n - 1) + 12 * n ^ 2 + 20 * n + 100
noncomputable def CU (n : ℝ) : ℝ := n * (n + 1) * (n + 2) / 3 + 6 * n ^ 2 + 10 * n + 100
noncomputable def eta4 (n : ℝ) : ℝ := 64 * (n ^ 2 - 5 * n + 10) / (n * (n - 1) * (n - 2) * (n - 3))
/-- `C(n, k)` as a real polynomial. -/
noncomputable def ch2 (n : ℝ) : ℝ := n * (n - 1) / 2
noncomputable def ch3 (n : ℝ) : ℝ := n * (n - 1) * (n - 2) / 6
noncomputable def ch4 (n : ℝ) : ℝ := n * (n - 1) * (n - 2) * (n - 3) / 24
noncomputable def ch6 (n : ℝ) : ℝ := n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 720
/-- The `Var/E²` bound for the level-6 floor. -/
noncomputable def V6 (n : ℝ) : ℝ :=
  (14 + 144 * (n - 6) + 743 / 1000 * 15 * ch2 (n - 6) + 6 / 25 * 20 * ch3 (n - 6) + 2 / 25 * 15 * ch4 (n - 6)) / ch6 n
/-- The level-4 `T`-part constant. -/
noncomputable def On (n : ℝ) : ℝ := kappa4 n / 4 * (54 + 54 * (n + 12) / (n + 8) ^ 2)
noncomputable def rho2 (n : ℝ) : ℝ := n * (n + 2)
noncomputable def rho3 (n : ℝ) : ℝ := n * (n + 2) * (n + 4)
/-- F-parts of the error second moments. -/
noncomputable def SFH2 (n : ℝ) : ℝ := (n + 7) / (n * (n + 2) ^ 2)
noncomputable def SFU2 (n : ℝ) : ℝ := SFH2 n + 2 / n
/-- Chaos-3 variances and covariances. -/
noncomputable def VDelta (n : ℝ) : ℝ := 3 / 32 * n * (n - 1) * (n - 2) + 9 / 8 * n * (n - 1) + 6 * n
noncomputable def VG3 (n : ℝ) : ℝ := n * (n + 3) / 2
noncomputable def VcK (n : ℝ) : ℝ := 2 * n + n * (n - 1) / 4
noncomputable def VX (n : ℝ) : ℝ := 2 * n ^ 2 + 4 * n + n ^ 2 * (n - 1) / 4
noncomputable def covDX (n : ℝ) : ℝ := 6 * n + 3 / 4 * n * (n - 1)
noncomputable def covXW (n : ℝ) : ℝ := 6 * n + 6 * n * (n - 1)
noncomputable def gam (n : ℝ) : ℝ := 1 / rho3 n - 3 / (n * rho2 n) + 2 / n ^ 3
/-- The T-part error second moment of a branch, as the four-group sum. -/
noncomputable def ST2 (n aCK actt aG atLL aDelta aX aW acLL : ℝ) : ℝ :=
  (aCK ^ 2 * VcK n + actt ^ 2 * (2 * n ^ 2) + 2 * aCK * actt * (2 * n))
  + (aG ^ 2 * VG3 n + atLL ^ 2 * (2 * n ^ 2) + 2 * aG * atLL * (2 * n))
  + (aDelta ^ 2 * VDelta n + aX ^ 2 * VX n + aW ^ 2 * (6 * n ^ 3) + 2 * aDelta * aX * covDX n
      + 2 * aDelta * aW * (6 * n) + 2 * aX * aW * covXW n)
  + acLL ^ 2 * (2 * n)
/-- Branch H. -/
noncomputable def STH2 (n : ℝ) : ℝ :=
  ST2 n (6 / rho2 n) 0 (6 / rho2 n) (-6 / (n * rho2 n)) (8 / rho3 n) (6 / (n * rho2 n) - 24 / (n * rho3 n)) (gam n) 0
/-- Branch U. -/
noncomputable def STU2 (n : ℝ) : ℝ :=
  ST2 n (6 / rho2 n) (-6 / (n * rho2 n)) (6 / rho2 n) (3 / n ^ 2 - 6 / (n * rho2 n)) (8 / rho3 n)
    (6 / (n * rho2 n) - 24 / (n * rho3 n)) (gam n - 6 / (n ^ 2 * rho2 n)) (3 / n)
noncomputable def SG2 (n : ℝ) : ℝ := (8 / rho3 n) ^ 2 * VDelta n

/-! ## Per-quantity bounds A1–A15 at `n = 6000 + t` (specification §2.1) -/

private lemma STH2_closed (n : ℝ) (hn : 0 < n) :
    STH2 n = 3 * (9*n^5 + 116*n^4 + 495*n^3 + 756*n^2 + 1024) /
      (n^3 * (n+2)^2 * (n+4)^2) := by
  have h2 : n + 2 ≠ 0 := ne_of_gt (by linarith)
  have h4 : n + 4 ≠ 0 := ne_of_gt (by linarith)
  simp only [STH2, ST2, rho2, rho3, gam, VcK, VG3, VDelta, VX, covDX, covXW]
  field_simp [ne_of_gt hn, h2, h4]
  ring

private lemma STU2_closed (n : ℝ) (hn : 0 < n) :
    STU2 n = 3 * (6*n^6 + 87*n^5 + 500*n^4 + 1359*n^3 + 1452*n^2 - 576*n - 128) /
      (n^3 * (n+2)^2 * (n+4)^2) := by
  have h2 : n + 2 ≠ 0 := ne_of_gt (by linarith)
  have h4 : n + 4 ≠ 0 := ne_of_gt (by linarith)
  simp only [STU2, ST2, rho2, rho3, gam, VcK, VG3, VDelta, VX, covDX, covXW]
  field_simp [ne_of_gt hn, h2, h4]
  ring

section bounds
variable (t : ℕ)

theorem A1 : (6000 + t : ℝ) ^ 2 * (SFH2 (6000 + t) / (kappa4 (6000 + t) / 4)) ≤ 803 / 200 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (803 / 200) - (n ^ 2 * (SFH2 n / (kappa4 n / 4))) = (253871162678364 + (3 * ((t : ℝ) ^ 4)) + (55188 * ((t : ℝ) ^ 3)) + (345307997 * ((t : ℝ) ^ 2)) + (775391842448 * (t : ℝ))) / (200 * (n - 1) * (n - 3) * (n - 2) * (2 + n)) := by
    simp only [kappa4, SFH2]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (253871162678364 + (3 * ((t : ℝ) ^ 4)) + (55188 * ((t : ℝ) ^ 3)) + (345307997 * ((t : ℝ) ^ 2)) + (775391842448 * (t : ℝ))) / (200 * (n - 1) * (n - 3) * (n - 2) * (2 + n)) := by positivity
  linarith


theorem A2 : (6000 + t : ℝ) * (SFU2 (6000 + t) / (kappa4 (6000 + t) / 4)) ≤ 321 / 40 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (321 / 40) - (n * (SFU2 n / (kappa4 n / 4))) = (15522843394548 + ((t : ℝ) ^ 4) + (18076 * ((t : ℝ) ^ 3)) + (109343199 * ((t : ℝ) ^ 2)) + (223910334576 * (t : ℝ))) / (40 * (n - 1) * (n - 3) * (n - 2) * (2 + n)) := by
    simp only [kappa4, SFU2, SFH2]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (15522843394548 + ((t : ℝ) ^ 4) + (18076 * ((t : ℝ) ^ 3)) + (109343199 * ((t : ℝ) ^ 2)) + (223910334576 * (t : ℝ))) / (40 * (n - 1) * (n - 3) * (n - 2) * (2 + n)) := by positivity
  linarith


theorem A3 : (6000 + t : ℝ) ^ 2 * STH2 (6000 + t) ≤ 2701 / 100 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (2701 / 100) - (n ^ 2 * STH2 n) = (4679414802892876800 + ((t : ℝ) ^ 5) + (27612 * ((t : ℝ) ^ 4)) + (302679952 * ((t : ℝ) ^ 3)) + (1644047168496 * ((t : ℝ) ^ 2)) + (4415899206124864 * (t : ℝ))) / (100 * n * ((2 + n) ^ 2) * ((4 + n) ^ 2)) := by
    rw [STH2_closed n hn]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (4679414802892876800 + ((t : ℝ) ^ 5) + (27612 * ((t : ℝ) ^ 4)) + (302679952 * ((t : ℝ) ^ 3)) + (1644047168496 * ((t : ℝ) ^ 2)) + (4415899206124864 * (t : ℝ))) / (100 * n * ((2 + n) ^ 2) * ((4 + n) ^ 2)) := by positivity
  linarith


theorem A4 : (6000 + t : ℝ) * STU2 (6000 + t) ≤ 1801 / 100 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (1801 / 100) - (n * STU2 n) = (11684234262804940838400 + ((t : ℝ) ^ 6) + (31512 * ((t : ℝ) ^ 5)) + (405303652 * ((t : ℝ) ^ 4)) + (2702967413196 * ((t : ℝ) ^ 3)) + (9733744605207664 * ((t : ℝ) ^ 2)) + (17525049965324140800 * (t : ℝ))) / (100 * (n ^ 2) * ((2 + n) ^ 2) * ((4 + n) ^ 2)) := by
    rw [STU2_closed n hn]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (11684234262804940838400 + ((t : ℝ) ^ 6) + (31512 * ((t : ℝ) ^ 5)) + (405303652 * ((t : ℝ) ^ 4)) + (2702967413196 * ((t : ℝ) ^ 3)) + (9733744605207664 * ((t : ℝ) ^ 2)) + (17525049965324140800 * (t : ℝ))) / (100 * (n ^ 2) * ((2 + n) ^ 2) * ((4 + n) ^ 2)) := by positivity
  linarith


theorem A5 : On (6000 + t) ≤ 27 / 2 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (27 / 2) - (On n) = (596702825201795256 + (459 * ((t : ℝ) ^ 4)) + (11024505 * ((t : ℝ) ^ 3)) + (99297138465 * ((t : ℝ) ^ 2)) + (397495121656950 * (t : ℝ))) / (2 * ((8 + n) ^ 2) * (2 + n) * (4 + n) * (6 + n)) := by
    simp only [On, kappa4]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (596702825201795256 + (459 * ((t : ℝ) ^ 4)) + (11024505 * ((t : ℝ) ^ 3)) + (99297138465 * ((t : ℝ) ^ 2)) + (397495121656950 * (t : ℝ))) / (2 * ((8 + n) ^ 2) * (2 + n) * (4 + n) * (6 + n)) := by positivity
  linarith


theorem A6 : 397 / 400 ≤ kappa6 (6000 + t) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (kappa6 n) - (397 / 400) = (94799344613339520 + (3 * ((t : ℝ) ^ 5)) + (72090 * ((t : ℝ) ^ 4)) + (650059020 * ((t : ℝ) ^ 3)) + (2609621555400 * ((t : ℝ) ^ 2)) + (3954844503169152 * (t : ℝ))) / (400 * (2 + n) * (4 + n) * (6 + n) * (8 + n) * (10 + n)) := by
    simp only [kappa6]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (94799344613339520 + (3 * ((t : ℝ) ^ 5)) + (72090 * ((t : ℝ) ^ 4)) + (650059020 * ((t : ℝ) ^ 3)) + (2609621555400 * ((t : ℝ) ^ 2)) + (3954844503169152 * (t : ℝ))) / (400 * (2 + n) * (4 + n) * (6 + n) * (8 + n) * (10 + n)) := by positivity
  linarith


theorem A7 : V6 (6000 + t) ≤ 11 / 10 ^ 7 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (11 / 10 ^ 7) - (V6 n) = (46461375225746092080000 + (11 * ((t : ℝ) ^ 6)) + (395835 * ((t : ℝ) ^ 5)) + (5575050935 * ((t : ℝ) ^ 4)) + (38825662437525 * ((t : ℝ) ^ 3)) + (135814482153453014 * ((t : ℝ) ^ 2)) + (201651449666562166680 * (t : ℝ))) / (10000000 * n * (n - 1) * (n - 5) * (n - 4) * (n - 3) * (n - 2)) := by
    simp only [V6, ch2, ch3, ch4, ch6]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (46461375225746092080000 + (11 * ((t : ℝ) ^ 6)) + (395835 * ((t : ℝ) ^ 5)) + (5575050935 * ((t : ℝ) ^ 4)) + (38825662437525 * ((t : ℝ) ^ 3)) + (135814482153453014 * ((t : ℝ) ^ 2)) + (201651449666562166680 * (t : ℝ))) / (10000000 * n * (n - 1) * (n - 5) * (n - 4) * (n - 3) * (n - 2)) := by positivity
  linarith


theorem A8 : eta4 (6000 + t) ≤ 9 / (5 * 10 ^ 6) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (9 / (5 * 10 ^ 6)) - (eta4 n) = (141936363676000 + (9 * ((t : ℝ) ^ 4)) + (215946 * ((t : ℝ) ^ 3)) + (1623028099 * ((t : ℝ) ^ 2)) + (3931769187946 * (t : ℝ))) / (5000000 * n * (n - 1) * (n - 3) * (n - 2)) := by
    simp only [eta4]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (141936363676000 + (9 * ((t : ℝ) ^ 4)) + (215946 * ((t : ℝ) ^ 3)) + (1623028099 * ((t : ℝ) ^ 2)) + (3931769187946 * (t : ℝ))) / (5000000 * n * (n - 1) * (n - 3) * (n - 2)) := by positivity
  linarith


theorem A9 : 1249 / 5000 ≤ P (6000 + t) / CH (6000 + t) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have hclosed : CH n = 100 + 2 * n ^ 3 + 13 * n ^ 2 + 19 * n := by
    unfold CH
    ring
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (P n / CH n) - (1249 / 5000) = (117325489100 + (2 * ((t : ℝ) ^ 3)) + (27263 * ((t : ℝ) ^ 2)) + (111132269 * (t : ℝ))) / (5000 * (100 + (2 * (n ^ 3)) + (13 * (n ^ 2)) + (19 * n))) := by
    rw [hclosed]
    simp only [P]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (117325489100 + (2 * ((t : ℝ) ^ 3)) + (27263 * ((t : ℝ) ^ 2)) + (111132269 * (t : ℝ))) / (5000 * (100 + (2 * (n ^ 3)) + (13 * (n ^ 2)) + (19 * n))) := by positivity
  linarith


theorem A10 : (6000 + t : ℝ) ^ 3 * SG2 (6000 + t) ≤ 6 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (6) - (n ^ 3 * SG2 n) = (3887571456384 + (18 * ((t : ℝ) ^ 3)) + (323988 * ((t : ℝ) ^ 2)) + (1943856576 * (t : ℝ))) / (((2 + n) ^ 2) * ((4 + n) ^ 2)) := by
    simp only [SG2, rho3, VDelta]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (3887571456384 + (18 * ((t : ℝ) ^ 3)) + (323988 * ((t : ℝ) ^ 2)) + (1943856576 * (t : ℝ))) / (((2 + n) ^ 2) * ((4 + n) ^ 2)) := by positivity
  linarith


theorem A11 : 1 / 7 ≤ (6000 + t : ℝ) * (P (6000 + t) / CG (6000 + t)) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (n * (P n / CG n)) - (1 / 7) = 5 / (7 * (16 + (7 * n))) := by
    simp only [P, CG]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < 5 / (7 * (16 + (7 * n))) := by positivity
  linarith


theorem A12 : CE (6000 + t) / P (6000 + t) ≤ 3 * (6000 + t : ℝ) ^ 2 + (6000 + t) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (3 * n ^ 2 + n) - (CE n / P n) = (18000 + (3 * (t : ℝ))) / (3 + n) := by
    simp only [P, CE]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (18000 + (3 * (t : ℝ))) / (3 + n) := by positivity
  linarith


theorem A13 : 100 * D (6000 + t) ≤ (D (6000 + t) / 1000 - 50) ^ 2 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : ((D n / 1000 - 50) ^ 2) - (100 * D n) = (11664852006649936 + ((1 / 4000000) * ((t : ℝ) ^ 6)) + ((18003 / 2000000) * ((t : ℝ) ^ 5)) + ((540180013 / 4000000) * ((t : ℝ) ^ 4)) + ((1080490028003 / 1000000) * ((t : ℝ) ^ 3)) + ((1458539450802989 / 125) * (t : ℝ)) + ((4862339651904001 / 1000000) * ((t : ℝ) ^ 2))) / 1 := by
    simp only [D]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (11664852006649936 + ((1 / 4000000) * ((t : ℝ) ^ 6)) + ((18003 / 2000000) * ((t : ℝ) ^ 5)) + ((540180013 / 4000000) * ((t : ℝ) ^ 4)) + ((1080490028003 / 1000000) * ((t : ℝ) ^ 3)) + ((1458539450802989 / 125) * (t : ℝ)) + ((4862339651904001 / 1000000) * ((t : ℝ) ^ 2))) / 1 := by positivity
  linarith


theorem A14 : 50 ≤ D (6000 + t) / 1000 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (D n / 1000) - (50) = (108053956 + ((1 / 2000) * ((t : ℝ) ^ 3)) + ((18003 / 2000) * ((t : ℝ) ^ 2)) + ((54018001 / 1000) * (t : ℝ))) / 1 := by
    simp only [D]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (108053956 + ((1 / 2000) * ((t : ℝ) ^ 3)) + ((18003 / 2000) * ((t : ℝ) ^ 2)) + ((54018001 / 1000) * (t : ℝ))) / 1 := by positivity
  linarith


theorem A15 : CU (6000 + t) < P (6000 + t) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (P n) - (CU n) = (35801935900 + ((1 / 6) * ((t : ℝ) ^ 3)) + ((5989 / 2) * ((t : ℝ) ^ 2)) + ((53801968 / 3) * (t : ℝ))) / 1 := by
    simp only [P, CU]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < (35801935900 + ((1 / 6) * ((t : ℝ) ^ 3)) + ((5989 / 2) * ((t : ℝ) ^ 2)) + ((53801968 / 3) * (t : ℝ))) / 1 := by positivity
  linarith


end bounds

/-! ## Window closures from the frozen constants (specification §2.1 B) -/

/-- `q ≤ δ_C`, the budget left for Chebyshev. -/
noncomputable def q : ℝ := 1 / 2 - (11 / 10 ^ 7) / (1 / 20) ^ 2 - 9 / (5 * 10 ^ 6) - 6 / 25 - 1 / 10 ^ 10
noncomputable def PhiLow : ℝ := 19 / 20 * (3 / 4) * (397 / 400)
noncomputable def cHat : ℝ := (27 / 2) / (6 / 25) * (1001 / 999)
noncomputable def SHatH : ℝ := 2701 / 100 * (1001 / 1000)
noncomputable def SHatU : ℝ := 1801 / 100 * (1001 / 1000)
noncomputable def sBarH : ℝ := 803 / 200
noncomputable def sBarU : ℝ := 321 / 40
noncomputable def kk : ℝ := 2 * q / 7
noncomputable def ll : ℝ := 2 * q * (1249 / 5000)
noncomputable def PhiLowG : ℝ := 1 / 2 * (3 / 4) * (397 / 400)

section windows
variable (t : ℕ)

theorem Bii_a : 0 < kk * (6000 + t) - sBarH := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (kk * n - sBarH) - (0) = ((7716483497 / 17500000) + ((2595581999 / 35000000000) * (t : ℝ))) / 1 := by
    simp only [sBarH, kk, q]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < ((7716483497 / 17500000) + ((2595581999 / 35000000000) * (t : ℝ))) / 1 := by positivity
  linarith


theorem Bii :
    sBarH ^ 2 * cHat ≤ (kk * (6000 + t) - sBarH) * (kk * PhiLow * (6000 + t) - sBarH * cHat - SHatH) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : ((kk * n - sBarH) * (kk * PhiLow * n - sBarH * cHat - SHatH)) - (sBarH ^ 2 * cHat) = ((9474916784010972072674957 / 362600000000000000000) + ((152452611977334545866629 / 39200000000000000000000000) * ((t : ℝ) ^ 2)) + ((30101137519430992923131207 / 1087800000000000000000000) * (t : ℝ))) / 1 := by
    simp only [PhiLow, cHat, SHatH, sBarH, kk, q]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < ((9474916784010972072674957 / 362600000000000000000) + ((152452611977334545866629 / 39200000000000000000000000) * ((t : ℝ) ^ 2)) + ((30101137519430992923131207 / 1087800000000000000000000) * (t : ℝ))) / 1 := by positivity
  linarith


theorem Biii_a : 0 < ll * (6000 + t) - sBarU := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (ll * n - sBarU) - (0) = ((9625333250253 / 12500000000) + ((3241881916751 / 25000000000000) * (t : ℝ))) / 1 := by
    simp only [sBarU, ll, q]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < ((9625333250253 / 12500000000) + ((3241881916751 / 25000000000000) * (t : ℝ))) / 1 := by positivity
  linarith


theorem Biii :
    sBarU ^ 2 * cHat ≤ (ll * (6000 + t) - sBarU) * (ll * PhiLow * (6000 + t) - sBarU * cHat - SHatU) := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : ((ll * n - sBarU) * (ll * PhiLow * n - sBarU * cHat - SHatU)) - (sBarU ^ 2 * cHat) = ((10705811732057297195384644007457 / 185000000000000000000000000) + ((237826227137253868886487106629 / 20000000000000000000000000000000) * ((t : ℝ) ^ 2)) + ((14979196755736097589097475085819 / 185000000000000000000000000000) * (t : ℝ))) / 1 := by
    simp only [PhiLow, cHat, SHatU, sBarU, ll, q]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < ((10705811732057297195384644007457 / 185000000000000000000000000) + ((237826227137253868886487106629 / 20000000000000000000000000000000) * ((t : ℝ) ^ 2)) + ((14979196755736097589097475085819 / 185000000000000000000000000000) * (t : ℝ))) / 1 := by positivity
  linarith


theorem Bi : 6 * (3 * (6000 + t : ℝ) + 1) < 2 * PhiLowG * (1 / 2 - 11 / 10 ^ 7 * 4) * (6000 + t) ^ 2 := by
  set n : ℝ := 6000 + t
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm1 : 0 < n - 1 := by dsimp [n]; linarith
  have hm2 : 0 < n - 2 := by dsimp [n]; linarith
  have hm3 : 0 < n - 3 := by dsimp [n]; linarith
  have hm4 : 0 < n - 4 := by dsimp [n]; linarith
  have hm5 : 0 < n - 5 := by dsimp [n]; linarith
  have hp2 : 0 < n + 2 := by positivity
  have hp4 : 0 < n + 4 := by positivity
  have hp6 : 0 < n + 6 := by positivity
  have hp8 : 0 < n + 8 := by positivity
  have hp10 : 0 < n + 10 := by positivity
  have key : (2 * PhiLowG * (1 / 2 - 11 / 10 ^ 7 * 4) * n ^ 2) - (6 * (3 * n + 1)) = ((13290626091 / 1000) + ((1488736899 / 4000000000) * ((t : ℝ) ^ 2)) + ((4448210697 / 1000000) * (t : ℝ))) / 1 := by
    simp only [PhiLowG]
    field_simp
    dsimp [n]
    ring
  have hpos : (0 : ℝ) < ((13290626091 / 1000) + ((1488736899 / 4000000000) * ((t : ℝ) ^ 2)) + ((4448210697 / 1000000) * (t : ℝ))) / 1 := by positivity
  linarith


end windows

/-! ## The quadratic certificate (specification §1.4) -/

/-- If `λ₀ > s = S_F²/φ` and `(λ₀ − s)(λ₀Φ − s c² − S'²) ≥ s²c²`, then for all `f, τ ≥ 0`,
`S_F² f² + S'² τ² ≤ λ₀ (Φ τ² + (max 0 (√φ f − c τ))²)`. -/
theorem quad_cert (SF2 phi c S2 Phi lam : ℝ) (hSF2 : 0 ≤ SF2) (hphi : 0 < phi) (hc : 0 ≤ c) (hS2 : 0 ≤ S2)
    (hlam : SF2 / phi < lam)
    (hcert : (SF2 / phi) ^ 2 * c ^ 2 ≤ (lam - SF2 / phi) * (lam * Phi - SF2 / phi * c ^ 2 - S2))
    (f τ : ℝ) (hf : 0 ≤ f) (hτ : 0 ≤ τ) :
    SF2 * f ^ 2 + S2 * τ ^ 2 ≤ lam * (Phi * τ ^ 2 + (max 0 (Real.sqrt phi * f - c * τ)) ^ 2) := by
  let s := SF2 / phi
  let y := Real.sqrt phi * f
  have hs : 0 ≤ s := div_nonneg hSF2 hphi.le
  have ha : 0 < lam - s := sub_pos.mpr hlam
  have hl : 0 < lam := lt_of_le_of_lt hs hlam
  have hy : 0 ≤ y := mul_nonneg (Real.sqrt_nonneg _) hf
  have hcτ : 0 ≤ c * τ := mul_nonneg hc hτ
  have hid : SF2 * f ^ 2 = s * y ^ 2 := by
    dsimp [s, y]
    rw [mul_pow, Real.sq_sqrt hphi.le]
    field_simp
  change s ^ 2 * c ^ 2 ≤ (lam - s) * (lam * Phi - s * c ^ 2 - S2) at hcert
  have hb : 0 ≤ lam * Phi - s * c ^ 2 - S2 := by
    have hnon : 0 ≤ (lam - s) * (lam * Phi - s * c ^ 2 - S2) :=
      le_trans (by positivity) hcert
    exact (mul_nonneg_iff_of_pos_left ha).mp hnon
  rw [hid]
  change s * y ^ 2 + S2 * τ ^ 2 ≤
    lam * (Phi * τ ^ 2 + (max 0 (y - c * τ)) ^ 2)
  by_cases hsmall : y ≤ c * τ
  · rw [max_eq_left (sub_nonpos.mpr hsmall)]
    have hsq : y ^ 2 ≤ (c * τ) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hs
    have hbudget := mul_nonneg hb (sq_nonneg τ)
    nlinarith
  · have hz : 0 ≤ y - c * τ := by linarith
    rw [max_eq_right hz]
    have hd : 0 ≤ (lam - s) * (lam * Phi - s * c ^ 2 - S2) - s ^ 2 * c ^ 2 :=
      sub_nonneg.mpr hcert
    have hsum := add_nonneg (sq_nonneg ((lam - s) * (y - c * τ) - s * c * τ))
      (mul_nonneg hd (sq_nonneg τ))
    have key :
        ((lam - s) * (y - c * τ) - s * c * τ) ^ 2 +
          ((lam - s) * (lam * Phi - s * c ^ 2 - S2) - s ^ 2 * c ^ 2) * τ ^ 2 =
        (lam - s) * (lam * (Phi * τ ^ 2 + (y - c * τ) ^ 2) -
          (s * y ^ 2 + S2 * τ ^ 2)) := by ring
    rw [key] at hsum
    have hgap := (mul_nonneg_iff_of_pos_left ha).mp hsum
    linarith

/-- The Laurent–Massart failure term: `2 e^{-25} ≤ 10^{-10}`. -/
theorem exp_neg25_small : 2 * Real.exp (-25) ≤ 1 / 10 ^ 10 := by
  have h1 : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have h25 : (27 / 10 : ℝ) ^ 25 ≤ Real.exp 25 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) h1 25
  have hlarge : (2 * 10 ^ 10 : ℝ) ≤ Real.exp 25 := by
    norm_num at h25 ⊢
    linarith
  rw [Real.exp_neg]
  have hp : 0 < Real.exp (25 : ℝ) := Real.exp_pos _
  have hi : (Real.exp (25 : ℝ))⁻¹ ≤ 1 / (2 * 10 ^ 10) := by
    rw [← one_div]
    exact (div_le_div_iff₀ hp (by norm_num)).2 (by simpa using hlarge)
  nlinarith

end BstLean.Part33
