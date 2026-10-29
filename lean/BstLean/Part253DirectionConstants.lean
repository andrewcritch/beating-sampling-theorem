import BstLean.Part253Roots

/-! Rational enclosures for the scalar constants in the direction formula. -/
namespace BstLean.Part253
open Real BstLean.Part152 BstLean.Part209

theorem gauss16_upper : gaussMomConst 16 ≤ 3.68794436 := by
  have h := root_upper (x := (1371195958099968000 : ℝ)) (b := (3.68794436 : ℝ))
    (by norm_num : (32 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [gaussMomConst, Nat.factorial]

theorem gauss32_upper : gaussMomConst 32 ≤ 5.05772465 := by
  have h := root_upper (x := (1130138339199322632554990773529330319360000000 : ℝ)) (b := (5.05772465 : ℝ))
    (by norm_num : (64 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [gaussMomConst, Nat.factorial]

theorem gauss64_upper : gaussMomConst 64 ≤ 7.02482392 := by
  have h := root_upper (x := (2340650764331144466221345754697091809049283736233503362096217361956854360782374130152842356326400000000000000 : ℝ)) (b := (7.02482392 : ℝ))
    (by norm_num : (128 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [gaussMomConst, Nat.factorial]

theorem gauss128_upper : gaussMomConst 128 ≤ 9.83214865 := by
  have h := root_upper (x := (131219850471532870280494180543930212298353497441690579517097209908251607023591082012615277517402188915738609914541751378117557938639583265587201015845713170909341970276087443974249733926280327057536337181401018889521520967680000000000000000000000000000000 : ℝ)) (b := (9.83214865 : ℝ))
    (by norm_num : (256 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [gaussMomConst, Nat.factorial]

theorem two16_upper : twoGaussConst 16 ≤ 3.76869983 := by
  have h := root_upper (x := (2742391916199936000 : ℝ)) (b := (3.76869983 : ℝ))
    (by norm_num : (32 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [twoGaussConst, Nat.factorial]

theorem two32_upper : twoGaussConst 32 ≤ 5.11279966 := by
  have h := root_upper (x := (2260276678398645265109981547058660638720000000 : ℝ)) (b := (5.11279966 : ℝ))
    (by norm_num : (64 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [twoGaussConst, Nat.factorial]

theorem two64_upper : twoGaussConst 64 ≤ 7.06296801 := by
  have h := root_upper (x := (4681301528662288932442691509394183618098567472467006724192434723913708721564748260305684712652800000000000000 : ℝ)) (b := (7.06296801 : ℝ))
    (by norm_num : (128 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [twoGaussConst, Nat.factorial]

theorem two128_upper : twoGaussConst 128 ≤ 9.85880631 := by
  have h := root_upper (x := (262439700943065740560988361087860424596706994883381159034194419816503214047182164025230555034804377831477219829083502756235115877279166531174402031691426341818683940552174887948499467852560654115072674362802037779043041935360000000000000000000000000000000 : ℝ)) (b := (9.85880631 : ℝ))
    (by norm_num : (256 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [twoGaussConst, Nat.factorial]

theorem factorial32_upper : factorialRoot 32 ≤ 12.79028928 := by
  have h := root_upper (x := (263130836933693530167218012160000000 : ℝ)) (b := (12.79028928 : ℝ))
    (by norm_num : (32 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [factorialRoot, Nat.factorial]

theorem factorial64_upper : factorialRoot 64 ≤ 24.67407549 := by
  have h := root_upper (x := (126886932185884164103433389335161480802865516174545192198801894375214704230400000000000000 : ℝ)) (b := (24.67407549 : ℝ))
    (by norm_num : (64 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [factorialRoot, Nat.factorial]

theorem overlap16_upper : (2 * ((16 : ℕ).factorial : ℝ)) ^ (1 / 32 : ℝ) ≤ 2.66487321 := by
  have h := root_upper (x := (41845579776000 : ℝ)) (b := (2.66487321 : ℝ))
    (by norm_num : (32 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [Nat.factorial]

theorem overlap32_upper : (2 * ((32 : ℕ).factorial : ℝ)) ^ (1 / 32 : ℝ) ≤ 13.07036015 := by
  have h := root_upper (x := (526261673867387060334436024320000000 : ℝ)) (b := (13.07036015 : ℝ))
    (by norm_num : (32 : ℕ) ≠ 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [Nat.factorial]

end BstLean.Part253
