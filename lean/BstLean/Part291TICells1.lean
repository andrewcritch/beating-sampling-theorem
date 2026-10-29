import BstLean.Part291GeometryBatch0
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters16 : Parameters where
  wlo := (189056793/500000000)
  whi := (728044459/1000000000)
  clo := (453378487/1000000000)
  chi := (77554357/125000000)
  wE := (668938269/1000000000)
  wS := (9/25)
  cE := (301315607/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (674714655581/1000000000000)
  cLam := (303548385109/500000000000)
  plane := (1/1)
  wRadius := (56915133/500000000)
  cRadius := (61427093/1000000000)

theorem lowTIParameters16_valid : Valid lowTIParameters16 := by
  constructor
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · have h : √((((668938269/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (160245521081/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters16,ta_lam] at h ⊢
    linarith
  · have h : √((((301315607/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (102890581609/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters16,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]
  · norm_num [lowTIParameters16]

theorem lowTISupply16 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters16 (117/250) (937/2000) := by
  refine ⟨lowTIParameters16_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum16W hn using 1 <;> norm_num [lowTIParameters16]
  · convert lowUniformNum16C hn using 1 <;> norm_num [lowTIParameters16]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry16W hn hθ).1 (by norm_num [lowTIParameters16])
      (by norm_num [lowTIParameters16]) (by norm_num [lowTIParameters16])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry16C hn hθ).1 (by norm_num [lowTIParameters16])
      (by norm_num [lowTIParameters16]) (by norm_num [lowTIParameters16])
  · intro θ hθ
    exact (lowGeometry16W hn hθ).2
  · intro θ hθ
    exact (lowGeometry16C hn hθ).2

noncomputable def lowTIParameters17 : Parameters where
  wlo := (189056793/500000000)
  whi := (728044459/1000000000)
  clo := (453378487/1000000000)
  chi := (77554357/125000000)
  wE := (668938269/1000000000)
  wS := (9/25)
  cE := (301315607/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (674714655581/1000000000000)
  cLam := (303548385109/500000000000)
  plane := (1/1)
  wRadius := (113884499/1000000000)
  cRadius := (61460369/1000000000)

theorem lowTIParameters17_valid : Valid lowTIParameters17 := by
  constructor
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · have h : √((((668938269/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (160245521081/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters17,ta_lam] at h ⊢
    linarith
  · have h : √((((301315607/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (102890581609/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters17,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]
  · norm_num [lowTIParameters17]

theorem lowTISupply17 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters17 (937/2000) (469/1000) := by
  refine ⟨lowTIParameters17_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum16W hn using 1 <;> norm_num [lowTIParameters17]
  · convert lowUniformNum16C hn using 1 <;> norm_num [lowTIParameters17]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry17W hn hθ).1 (by norm_num [lowTIParameters17])
      (by norm_num [lowTIParameters17]) (by norm_num [lowTIParameters17])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry17C hn hθ).1 (by norm_num [lowTIParameters17])
      (by norm_num [lowTIParameters17]) (by norm_num [lowTIParameters17])
  · intro θ hθ
    exact (lowGeometry17W hn hθ).2
  · intro θ hθ
    exact (lowGeometry17C hn hθ).2

noncomputable def lowTIParameters18 : Parameters where
  wlo := (75418381/200000000)
  whi := (727125683/1000000000)
  clo := (452369839/1000000000)
  chi := (309729467/500000000)
  wE := (167076661/250000000)
  wS := (9/25)
  cE := (602089383/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (33704721839/50000000000)
  cLam := (18955025809/31250000000)
  plane := (1/1)
  wRadius := (14242333/125000000)
  cRadius := (61493613/1000000000)

theorem lowTIParameters18_valid : Valid lowTIParameters18 := by
  constructor
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · have h : √((((167076661/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (7997055739/50000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters18,ta_lam] at h ⊢
    linarith
  · have h : √((((602089383/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (51379033597/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters18,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]
  · norm_num [lowTIParameters18]

theorem lowTISupply18 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters18 (469/1000) (939/2000) := by
  refine ⟨lowTIParameters18_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum18W hn using 1 <;> norm_num [lowTIParameters18]
  · convert lowUniformNum18C hn using 1 <;> norm_num [lowTIParameters18]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry18W hn hθ).1 (by norm_num [lowTIParameters18])
      (by norm_num [lowTIParameters18]) (by norm_num [lowTIParameters18])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry18C hn hθ).1 (by norm_num [lowTIParameters18])
      (by norm_num [lowTIParameters18]) (by norm_num [lowTIParameters18])
  · intro θ hθ
    exact (lowGeometry18W hn hθ).2
  · intro θ hθ
    exact (lowGeometry18C hn hθ).2

noncomputable def lowTIParameters19 : Parameters where
  wlo := (75418381/200000000)
  whi := (727125683/1000000000)
  clo := (452369839/1000000000)
  chi := (309729467/500000000)
  wE := (167076661/250000000)
  wS := (9/25)
  cE := (602089383/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (33704721839/50000000000)
  cLam := (18955025809/31250000000)
  plane := (1/1)
  wRadius := (113992761/1000000000)
  cRadius := (2461073/40000000)

theorem lowTIParameters19_valid : Valid lowTIParameters19 := by
  constructor
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · have h : √((((167076661/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (7997055739/50000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters19,ta_lam] at h ⊢
    linarith
  · have h : √((((602089383/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (51379033597/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters19,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]
  · norm_num [lowTIParameters19]

theorem lowTISupply19 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters19 (939/2000) (47/100) := by
  refine ⟨lowTIParameters19_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum18W hn using 1 <;> norm_num [lowTIParameters19]
  · convert lowUniformNum18C hn using 1 <;> norm_num [lowTIParameters19]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry19W hn hθ).1 (by norm_num [lowTIParameters19])
      (by norm_num [lowTIParameters19]) (by norm_num [lowTIParameters19])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry19C hn hθ).1 (by norm_num [lowTIParameters19])
      (by norm_num [lowTIParameters19]) (by norm_num [lowTIParameters19])
  · intro θ hθ
    exact (lowGeometry19W hn hθ).2
  · intro θ hθ
    exact (lowGeometry19C hn hθ).2

noncomputable def lowTIParameters20 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114046791/1000000000)
  cRadius := (12312001/200000000)

theorem lowTIParameters20_valid : Valid lowTIParameters20 := by
  constructor
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters20,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters20,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]
  · norm_num [lowTIParameters20]

theorem lowTISupply20 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters20 (47/100) (941/2000) := by
  refine ⟨lowTIParameters20_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters20]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters20]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry20W hn hθ).1 (by norm_num [lowTIParameters20])
      (by norm_num [lowTIParameters20]) (by norm_num [lowTIParameters20])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry20C hn hθ).1 (by norm_num [lowTIParameters20])
      (by norm_num [lowTIParameters20]) (by norm_num [lowTIParameters20])
  · intro θ hθ
    exact (lowGeometry20W hn hθ).2
  · intro θ hθ
    exact (lowGeometry20C hn hθ).2

noncomputable def lowTIParameters21 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (57050377/500000000)
  cRadius := (962393/15625000)

theorem lowTIParameters21_valid : Valid lowTIParameters21 := by
  constructor
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters21,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters21,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]
  · norm_num [lowTIParameters21]

theorem lowTISupply21 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters21 (941/2000) (471/1000) := by
  refine ⟨lowTIParameters21_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters21]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters21]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry21W hn hθ).1 (by norm_num [lowTIParameters21])
      (by norm_num [lowTIParameters21]) (by norm_num [lowTIParameters21])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry21C hn hθ).1 (by norm_num [lowTIParameters21])
      (by norm_num [lowTIParameters21]) (by norm_num [lowTIParameters21])
  · intro θ hθ
    exact (lowGeometry21W hn hθ).2
  · intro θ hθ
    exact (lowGeometry21C hn hθ).2

noncomputable def lowTIParameters22 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (2283093/20000000)
  cRadius := (61626267/1000000000)

theorem lowTIParameters22_valid : Valid lowTIParameters22 := by
  constructor
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters22,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters22,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]
  · norm_num [lowTIParameters22]

theorem lowTISupply22 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters22 (471/1000) (943/2000) := by
  refine ⟨lowTIParameters22_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters22]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters22]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry22W hn hθ).1 (by norm_num [lowTIParameters22])
      (by norm_num [lowTIParameters22]) (by norm_num [lowTIParameters22])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry22C hn hθ).1 (by norm_num [lowTIParameters22])
      (by norm_num [lowTIParameters22]) (by norm_num [lowTIParameters22])
  · intro θ hθ
    exact (lowGeometry22W hn hθ).2
  · intro θ hθ
    exact (lowGeometry22C hn hθ).2

noncomputable def lowTIParameters23 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (57104239/500000000)
  cRadius := (61659349/1000000000)

theorem lowTIParameters23_valid : Valid lowTIParameters23 := by
  constructor
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters23,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters23,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]
  · norm_num [lowTIParameters23]

theorem lowTISupply23 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters23 (943/2000) (59/125) := by
  refine ⟨lowTIParameters23_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters23]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters23]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry23W hn hθ).1 (by norm_num [lowTIParameters23])
      (by norm_num [lowTIParameters23]) (by norm_num [lowTIParameters23])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry23C hn hθ).1 (by norm_num [lowTIParameters23])
      (by norm_num [lowTIParameters23]) (by norm_num [lowTIParameters23])
  · intro θ hθ
    exact (lowGeometry23W hn hθ).2
  · intro θ hθ
    exact (lowGeometry23C hn hθ).2

noncomputable def lowTIParameters24 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (57131119/500000000)
  cRadius := (61692399/1000000000)

theorem lowTIParameters24_valid : Valid lowTIParameters24 := by
  constructor
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters24,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters24,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]
  · norm_num [lowTIParameters24]

theorem lowTISupply24 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters24 (59/125) (189/400) := by
  refine ⟨lowTIParameters24_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters24]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters24]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry24W hn hθ).1 (by norm_num [lowTIParameters24])
      (by norm_num [lowTIParameters24]) (by norm_num [lowTIParameters24])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry24C hn hθ).1 (by norm_num [lowTIParameters24])
      (by norm_num [lowTIParameters24]) (by norm_num [lowTIParameters24])
  · intro θ hθ
    exact (lowGeometry24W hn hθ).2
  · intro θ hθ
    exact (lowGeometry24C hn hθ).2

noncomputable def lowTIParameters25 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114315931/1000000000)
  cRadius := (61725417/1000000000)

theorem lowTIParameters25_valid : Valid lowTIParameters25 := by
  constructor
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters25,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters25,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]
  · norm_num [lowTIParameters25]

theorem lowTISupply25 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters25 (189/400) (473/1000) := by
  refine ⟨lowTIParameters25_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters25]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters25]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry25W hn hθ).1 (by norm_num [lowTIParameters25])
      (by norm_num [lowTIParameters25]) (by norm_num [lowTIParameters25])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry25C hn hθ).1 (by norm_num [lowTIParameters25])
      (by norm_num [lowTIParameters25]) (by norm_num [lowTIParameters25])
  · intro θ hθ
    exact (lowGeometry25W hn hθ).2
  · intro θ hθ
    exact (lowGeometry25C hn hθ).2

noncomputable def lowTIParameters26 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114369557/1000000000)
  cRadius := (30879201/500000000)

theorem lowTIParameters26_valid : Valid lowTIParameters26 := by
  constructor
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters26,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters26,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]
  · norm_num [lowTIParameters26]

theorem lowTISupply26 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters26 (473/1000) (947/2000) := by
  refine ⟨lowTIParameters26_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters26]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters26]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry26W hn hθ).1 (by norm_num [lowTIParameters26])
      (by norm_num [lowTIParameters26]) (by norm_num [lowTIParameters26])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry26C hn hθ).1 (by norm_num [lowTIParameters26])
      (by norm_num [lowTIParameters26]) (by norm_num [lowTIParameters26])
  · intro θ hθ
    exact (lowGeometry26W hn hθ).2
  · intro θ hθ
    exact (lowGeometry26C hn hθ).2

noncomputable def lowTIParameters27 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (28605779/250000000)
  cRadius := (15447839/250000000)

theorem lowTIParameters27_valid : Valid lowTIParameters27 := by
  constructor
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters27,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters27,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]
  · norm_num [lowTIParameters27]

theorem lowTISupply27 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters27 (947/2000) (237/500) := by
  refine ⟨lowTIParameters27_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters27]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters27]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry27W hn hθ).1 (by norm_num [lowTIParameters27])
      (by norm_num [lowTIParameters27]) (by norm_num [lowTIParameters27])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry27C hn hθ).1 (by norm_num [lowTIParameters27])
      (by norm_num [lowTIParameters27]) (by norm_num [lowTIParameters27])
  · intro θ hθ
    exact (lowGeometry27W hn hθ).2
  · intro θ hθ
    exact (lowGeometry27C hn hθ).2

noncomputable def lowTIParameters28 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114476607/1000000000)
  cRadius := (15456069/250000000)

theorem lowTIParameters28_valid : Valid lowTIParameters28 := by
  constructor
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters28,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters28,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]
  · norm_num [lowTIParameters28]

theorem lowTISupply28 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters28 (237/500) (949/2000) := by
  refine ⟨lowTIParameters28_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters28]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters28]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry28W hn hθ).1 (by norm_num [lowTIParameters28])
      (by norm_num [lowTIParameters28]) (by norm_num [lowTIParameters28])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry28C hn hθ).1 (by norm_num [lowTIParameters28])
      (by norm_num [lowTIParameters28]) (by norm_num [lowTIParameters28])
  · intro θ hθ
    exact (lowGeometry28W hn hθ).2
  · intro θ hθ
    exact (lowGeometry28C hn hθ).2

noncomputable def lowTIParameters29 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114530031/1000000000)
  cRadius := (12371433/200000000)

theorem lowTIParameters29_valid : Valid lowTIParameters29 := by
  constructor
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters29,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters29,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]
  · norm_num [lowTIParameters29]

theorem lowTISupply29 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters29 (949/2000) (19/40) := by
  refine ⟨lowTIParameters29_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters29]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters29]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry29W hn hθ).1 (by norm_num [lowTIParameters29])
      (by norm_num [lowTIParameters29]) (by norm_num [lowTIParameters29])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry29C hn hθ).1 (by norm_num [lowTIParameters29])
      (by norm_num [lowTIParameters29]) (by norm_num [lowTIParameters29])
  · intro θ hθ
    exact (lowGeometry29W hn hθ).2
  · intro θ hθ
    exact (lowGeometry29C hn hθ).2

noncomputable def lowTIParameters30 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (28645847/250000000)
  cRadius := (61890021/1000000000)

theorem lowTIParameters30_valid : Valid lowTIParameters30 := by
  constructor
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters30,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters30,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]
  · norm_num [lowTIParameters30]

theorem lowTISupply30 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters30 (19/40) (951/2000) := by
  refine ⟨lowTIParameters30_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters30]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters30]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry30W hn hθ).1 (by norm_num [lowTIParameters30])
      (by norm_num [lowTIParameters30]) (by norm_num [lowTIParameters30])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry30C hn hθ).1 (by norm_num [lowTIParameters30])
      (by norm_num [lowTIParameters30]) (by norm_num [lowTIParameters30])
  · intro θ hθ
    exact (lowGeometry30W hn hθ).2
  · intro θ hθ
    exact (lowGeometry30C hn hθ).2

noncomputable def lowTIParameters31 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114636677/1000000000)
  cRadius := (12384569/200000000)

theorem lowTIParameters31_valid : Valid lowTIParameters31 := by
  constructor
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters31,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters31,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]
  · norm_num [lowTIParameters31]

theorem lowTISupply31 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters31 (951/2000) (119/250) := by
  refine ⟨lowTIParameters31_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters31]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters31]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry31W hn hθ).1 (by norm_num [lowTIParameters31])
      (by norm_num [lowTIParameters31]) (by norm_num [lowTIParameters31])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry31C hn hθ).1 (by norm_num [lowTIParameters31])
      (by norm_num [lowTIParameters31]) (by norm_num [lowTIParameters31])
  · intro θ hθ
    exact (lowGeometry31W hn hθ).2
  · intro θ hθ
    exact (lowGeometry31C hn hθ).2

end BstLean.BlueprintLow
