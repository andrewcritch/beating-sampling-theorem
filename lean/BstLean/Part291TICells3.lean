import BstLean.Part291GeometryBatch1
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters48 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (28883077/250000000)
  cRadius := (62475913/1000000000)

theorem lowTIParameters48_valid : Valid lowTIParameters48 := by
  constructor
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters48,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters48,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]
  · norm_num [lowTIParameters48]

theorem lowTISupply48 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters48 (121/250) (969/2000) := by
  refine ⟨lowTIParameters48_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters48]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters48]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry48W hn hθ).1 (by norm_num [lowTIParameters48])
      (by norm_num [lowTIParameters48]) (by norm_num [lowTIParameters48])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry48C hn hθ).1 (by norm_num [lowTIParameters48])
      (by norm_num [lowTIParameters48]) (by norm_num [lowTIParameters48])
  · intro θ hθ
    exact (lowGeometry48W hn hθ).2
  · intro θ hθ
    exact (lowGeometry48C hn hθ).2

noncomputable def lowTIParameters49 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (28896097/250000000)
  cRadius := (15627039/250000000)

theorem lowTIParameters49_valid : Valid lowTIParameters49 := by
  constructor
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters49,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters49,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]
  · norm_num [lowTIParameters49]

theorem lowTISupply49 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters49 (969/2000) (97/200) := by
  refine ⟨lowTIParameters49_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters49]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters49]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry49W hn hθ).1 (by norm_num [lowTIParameters49])
      (by norm_num [lowTIParameters49]) (by norm_num [lowTIParameters49])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry49C hn hθ).1 (by norm_num [lowTIParameters49])
      (by norm_num [lowTIParameters49]) (by norm_num [lowTIParameters49])
  · intro θ hθ
    exact (lowGeometry49W hn hθ).2
  · intro θ hθ
    exact (lowGeometry49C hn hθ).2

noncomputable def lowTIParameters50 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (289091/2500000)
  cRadius := (62540367/1000000000)

theorem lowTIParameters50_valid : Valid lowTIParameters50 := by
  constructor
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters50,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters50,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]
  · norm_num [lowTIParameters50]

theorem lowTISupply50 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters50 (97/200) (971/2000) := by
  refine ⟨lowTIParameters50_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters50]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters50]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry50W hn hθ).1 (by norm_num [lowTIParameters50])
      (by norm_num [lowTIParameters50]) (by norm_num [lowTIParameters50])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry50C hn hθ).1 (by norm_num [lowTIParameters50])
      (by norm_num [lowTIParameters50]) (by norm_num [lowTIParameters50])
  · intro θ hθ
    exact (lowGeometry50W hn hθ).2
  · intro θ hθ
    exact (lowGeometry50C hn hθ).2

noncomputable def lowTIParameters51 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (23137669/200000000)
  cRadius := (31286273/500000000)

theorem lowTIParameters51_valid : Valid lowTIParameters51 := by
  constructor
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters51,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters51,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]
  · norm_num [lowTIParameters51]

theorem lowTISupply51 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters51 (971/2000) (243/500) := by
  refine ⟨lowTIParameters51_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters51]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters51]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry51W hn hθ).1 (by norm_num [lowTIParameters51])
      (by norm_num [lowTIParameters51]) (by norm_num [lowTIParameters51])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry51C hn hθ).1 (by norm_num [lowTIParameters51])
      (by norm_num [lowTIParameters51]) (by norm_num [lowTIParameters51])
  · intro θ hθ
    exact (lowGeometry51W hn hθ).2
  · intro θ hθ
    exact (lowGeometry51C hn hθ).2

noncomputable def lowTIParameters52 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (115740223/1000000000)
  cRadius := (15651173/250000000)

theorem lowTIParameters52_valid : Valid lowTIParameters52 := by
  constructor
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters52,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters52,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]
  · norm_num [lowTIParameters52]

theorem lowTISupply52 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters52 (243/500) (973/2000) := by
  refine ⟨lowTIParameters52_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters52]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters52]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry52W hn hθ).1 (by norm_num [lowTIParameters52])
      (by norm_num [lowTIParameters52]) (by norm_num [lowTIParameters52])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry52C hn hθ).1 (by norm_num [lowTIParameters52])
      (by norm_num [lowTIParameters52]) (by norm_num [lowTIParameters52])
  · intro θ hθ
    exact (lowGeometry52W hn hθ).2
  · intro θ hθ
    exact (lowGeometry52C hn hθ).2

noncomputable def lowTIParameters53 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (57896017/500000000)
  cRadius := (31318403/500000000)

theorem lowTIParameters53_valid : Valid lowTIParameters53 := by
  constructor
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters53,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters53,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]
  · norm_num [lowTIParameters53]

theorem lowTISupply53 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters53 (973/2000) (487/1000) := by
  refine ⟨lowTIParameters53_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters53]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters53]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry53W hn hθ).1 (by norm_num [lowTIParameters53])
      (by norm_num [lowTIParameters53]) (by norm_num [lowTIParameters53])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry53C hn hθ).1 (by norm_num [lowTIParameters53])
      (by norm_num [lowTIParameters53]) (by norm_num [lowTIParameters53])
  · intro θ hθ
    exact (lowGeometry53W hn hθ).2
  · intro θ hθ
    exact (lowGeometry53C hn hθ).2

noncomputable def lowTIParameters54 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (57921889/500000000)
  cRadius := (7833611/125000000)

theorem lowTIParameters54_valid : Valid lowTIParameters54 := by
  constructor
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters54,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters54,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]
  · norm_num [lowTIParameters54]

theorem lowTISupply54 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters54 (487/1000) (39/80) := by
  refine ⟨lowTIParameters54_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters54]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters54]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry54W hn hθ).1 (by norm_num [lowTIParameters54])
      (by norm_num [lowTIParameters54]) (by norm_num [lowTIParameters54])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry54C hn hθ).1 (by norm_num [lowTIParameters54])
      (by norm_num [lowTIParameters54]) (by norm_num [lowTIParameters54])
  · intro θ hθ
    exact (lowGeometry54W hn hθ).2
  · intro θ hθ
    exact (lowGeometry54C hn hθ).2

noncomputable def lowTIParameters55 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (23179091/200000000)
  cRadius := (31350469/500000000)

theorem lowTIParameters55_valid : Valid lowTIParameters55 := by
  constructor
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters55,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters55,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]
  · norm_num [lowTIParameters55]

theorem lowTISupply55 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters55 (39/80) (61/125) := by
  refine ⟨lowTIParameters55_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters55]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters55]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry55W hn hθ).1 (by norm_num [lowTIParameters55])
      (by norm_num [lowTIParameters55]) (by norm_num [lowTIParameters55])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry55C hn hθ).1 (by norm_num [lowTIParameters55])
      (by norm_num [lowTIParameters55]) (by norm_num [lowTIParameters55])
  · intro θ hθ
    exact (lowGeometry55W hn hθ).2
  · intro θ hθ
    exact (lowGeometry55C hn hθ).2

noncomputable def lowTIParameters56 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (23189413/200000000)
  cRadius := (15683239/250000000)

theorem lowTIParameters56_valid : Valid lowTIParameters56 := by
  constructor
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters56,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters56,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]
  · norm_num [lowTIParameters56]

theorem lowTISupply56 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters56 (61/125) (977/2000) := by
  refine ⟨lowTIParameters56_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters56]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters56]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry56W hn hθ).1 (by norm_num [lowTIParameters56])
      (by norm_num [lowTIParameters56]) (by norm_num [lowTIParameters56])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry56C hn hθ).1 (by norm_num [lowTIParameters56])
      (by norm_num [lowTIParameters56]) (by norm_num [lowTIParameters56])
  · intro θ hθ
    exact (lowGeometry56W hn hθ).2
  · intro θ hθ
    exact (lowGeometry56C hn hθ).2

noncomputable def lowTIParameters57 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (115998607/1000000000)
  cRadius := (62764941/1000000000)

theorem lowTIParameters57_valid : Valid lowTIParameters57 := by
  constructor
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters57,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters57,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]
  · norm_num [lowTIParameters57]

theorem lowTISupply57 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters57 (977/2000) (489/1000) := by
  refine ⟨lowTIParameters57_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters57]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters57]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry57W hn hθ).1 (by norm_num [lowTIParameters57])
      (by norm_num [lowTIParameters57]) (by norm_num [lowTIParameters57])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry57C hn hθ).1 (by norm_num [lowTIParameters57])
      (by norm_num [lowTIParameters57]) (by norm_num [lowTIParameters57])
  · intro θ hθ
    exact (lowGeometry57W hn hθ).2
  · intro θ hθ
    exact (lowGeometry57C hn hθ).2

noncomputable def lowTIParameters58 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (58025041/500000000)
  cRadius := (31398447/500000000)

theorem lowTIParameters58_valid : Valid lowTIParameters58 := by
  constructor
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters58,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters58,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]
  · norm_num [lowTIParameters58]

theorem lowTISupply58 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters58 (489/1000) (979/2000) := by
  refine ⟨lowTIParameters58_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters58]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters58]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry58W hn hθ).1 (by norm_num [lowTIParameters58])
      (by norm_num [lowTIParameters58]) (by norm_num [lowTIParameters58])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry58C hn hθ).1 (by norm_num [lowTIParameters58])
      (by norm_num [lowTIParameters58]) (by norm_num [lowTIParameters58])
  · intro θ hθ
    exact (lowGeometry58W hn hθ).2
  · intro θ hθ
    exact (lowGeometry58C hn hθ).2

noncomputable def lowTIParameters59 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (116101491/1000000000)
  cRadius := (12565763/200000000)

theorem lowTIParameters59_valid : Valid lowTIParameters59 := by
  constructor
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters59,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters59,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]
  · norm_num [lowTIParameters59]

theorem lowTISupply59 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters59 (979/2000) (49/100) := by
  refine ⟨lowTIParameters59_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters59]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters59]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry59W hn hθ).1 (by norm_num [lowTIParameters59])
      (by norm_num [lowTIParameters59]) (by norm_num [lowTIParameters59])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry59C hn hθ).1 (by norm_num [lowTIParameters59])
      (by norm_num [lowTIParameters59]) (by norm_num [lowTIParameters59])
  · intro θ hθ
    exact (lowGeometry59W hn hθ).2
  · intro θ hθ
    exact (lowGeometry59C hn hθ).2

noncomputable def lowTIParameters60 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (226861/1953125)
  cRadius := (1964397/31250000)

theorem lowTIParameters60_valid : Valid lowTIParameters60 := by
  constructor
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters60,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters60,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]
  · norm_num [lowTIParameters60]

theorem lowTISupply60 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters60 (49/100) (981/2000) := by
  refine ⟨lowTIParameters60_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters60]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters60]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry60W hn hθ).1 (by norm_num [lowTIParameters60])
      (by norm_num [lowTIParameters60]) (by norm_num [lowTIParameters60])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry60C hn hθ).1 (by norm_num [lowTIParameters60])
      (by norm_num [lowTIParameters60]) (by norm_num [lowTIParameters60])
  · intro θ hθ
    exact (lowGeometry60W hn hθ).2
  · intro θ hθ
    exact (lowGeometry60C hn hθ).2

noncomputable def lowTIParameters61 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (58102053/500000000)
  cRadius := (62892561/1000000000)

theorem lowTIParameters61_valid : Valid lowTIParameters61 := by
  constructor
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters61,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters61,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]
  · norm_num [lowTIParameters61]

theorem lowTISupply61 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters61 (981/2000) (491/1000) := by
  refine ⟨lowTIParameters61_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters61]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters61]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry61W hn hθ).1 (by norm_num [lowTIParameters61])
      (by norm_num [lowTIParameters61]) (by norm_num [lowTIParameters61])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry61C hn hθ).1 (by norm_num [lowTIParameters61])
      (by norm_num [lowTIParameters61]) (by norm_num [lowTIParameters61])
  · intro θ hθ
    exact (lowGeometry61W hn hθ).2
  · intro θ hθ
    exact (lowGeometry61C hn hθ).2

noncomputable def lowTIParameters62 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (116255313/1000000000)
  cRadius := (12584877/200000000)

theorem lowTIParameters62_valid : Valid lowTIParameters62 := by
  constructor
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters62,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters62,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]
  · norm_num [lowTIParameters62]

theorem lowTISupply62 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters62 (491/1000) (983/2000) := by
  refine ⟨lowTIParameters62_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters62]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters62]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry62W hn hθ).1 (by norm_num [lowTIParameters62])
      (by norm_num [lowTIParameters62]) (by norm_num [lowTIParameters62])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry62C hn hθ).1 (by norm_num [lowTIParameters62])
      (by norm_num [lowTIParameters62]) (by norm_num [lowTIParameters62])
  · intro θ hθ
    exact (lowGeometry62W hn hθ).2
  · intro θ hθ
    exact (lowGeometry62C hn hθ).2

noncomputable def lowTIParameters63 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (116306453/1000000000)
  cRadius := (62956177/1000000000)

theorem lowTIParameters63_valid : Valid lowTIParameters63 := by
  constructor
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters63,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters63,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]
  · norm_num [lowTIParameters63]

theorem lowTISupply63 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters63 (983/2000) (123/250) := by
  refine ⟨lowTIParameters63_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters63]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters63]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry63W hn hθ).1 (by norm_num [lowTIParameters63])
      (by norm_num [lowTIParameters63]) (by norm_num [lowTIParameters63])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry63C hn hθ).1 (by norm_num [lowTIParameters63])
      (by norm_num [lowTIParameters63]) (by norm_num [lowTIParameters63])
  · intro θ hθ
    exact (lowGeometry63W hn hθ).2
  · intro θ hθ
    exact (lowGeometry63C hn hθ).2

end BstLean.BlueprintLow
