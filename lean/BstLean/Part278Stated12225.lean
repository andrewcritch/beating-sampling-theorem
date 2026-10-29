import BstLean.Part278Row

/-!
# Part 278 (O5): the stated program on the 12 225–12 349 family, odd and even

Even `n`: `statedDesign_even` and `Part267.classifier_12225_12349`. Odd `n`:
`classifier_from_row_st` on the row `Part267.row<n>`, with `OddRoot` from `oddRoot_row`. The three
events come from the row's own base event `sourceBase` (no new event, no new charge).
-/

namespace BstLean.Part278

open BstLean.Part130 BstLean.Part157

theorem stated_odd_12225 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12225) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12225 t
    (oddRoot_row BstLean.Part267.row12225 (by norm_num) ⟨6112, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12227 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12227).prod (sampMeas (10 ^ 12) 12227)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12227) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12227 t
    (oddRoot_row BstLean.Part267.row12227 (by norm_num) ⟨6113, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12229 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12229).prod (sampMeas (10 ^ 12) 12229)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12229) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12229 t
    (oddRoot_row BstLean.Part267.row12229 (by norm_num) ⟨6114, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12231 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12231).prod (sampMeas (10 ^ 12) 12231)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12231) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12231 t
    (oddRoot_row BstLean.Part267.row12231 (by norm_num) ⟨6115, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12233 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12233).prod (sampMeas (10 ^ 12) 12233)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12233) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12233 t
    (oddRoot_row BstLean.Part267.row12233 (by norm_num) ⟨6116, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12235 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12235).prod (sampMeas (10 ^ 12) 12235)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12235) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12235 t
    (oddRoot_row BstLean.Part267.row12235 (by norm_num) ⟨6117, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12237 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12237).prod (sampMeas (10 ^ 12) 12237)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12237) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12237 t
    (oddRoot_row BstLean.Part267.row12237 (by norm_num) ⟨6118, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12239 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12239).prod (sampMeas (10 ^ 12) 12239)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12239) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12239 t
    (oddRoot_row BstLean.Part267.row12239 (by norm_num) ⟨6119, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12241 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12241).prod (sampMeas (10 ^ 12) 12241)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12241) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12241 t
    (oddRoot_row BstLean.Part267.row12241 (by norm_num) ⟨6120, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12243 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12243).prod (sampMeas (10 ^ 12) 12243)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12243) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12243 t
    (oddRoot_row BstLean.Part267.row12243 (by norm_num) ⟨6121, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12245 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12245).prod (sampMeas (10 ^ 12) 12245)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12245) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12245 t
    (oddRoot_row BstLean.Part267.row12245 (by norm_num) ⟨6122, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12247 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12247).prod (sampMeas (10 ^ 12) 12247)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12247) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12247 t
    (oddRoot_row BstLean.Part267.row12247 (by norm_num) ⟨6123, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12249 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12249).prod (sampMeas (10 ^ 12) 12249)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12249) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12249 t
    (oddRoot_row BstLean.Part267.row12249 (by norm_num) ⟨6124, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12251 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12251).prod (sampMeas (10 ^ 12) 12251)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12251) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12251 t
    (oddRoot_row BstLean.Part267.row12251 (by norm_num) ⟨6125, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12253 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12253).prod (sampMeas (10 ^ 12) 12253)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12253) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12253 t
    (oddRoot_row BstLean.Part267.row12253 (by norm_num) ⟨6126, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12255 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12255).prod (sampMeas (10 ^ 12) 12255)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12255) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12255 t
    (oddRoot_row BstLean.Part267.row12255 (by norm_num) ⟨6127, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12257 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12257).prod (sampMeas (10 ^ 12) 12257)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12257) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12257 t
    (oddRoot_row BstLean.Part267.row12257 (by norm_num) ⟨6128, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12259 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12259).prod (sampMeas (10 ^ 12) 12259)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12259) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12259 t
    (oddRoot_row BstLean.Part267.row12259 (by norm_num) ⟨6129, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12261 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12261).prod (sampMeas (10 ^ 12) 12261)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12261) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12261 t
    (oddRoot_row BstLean.Part267.row12261 (by norm_num) ⟨6130, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12263 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12263).prod (sampMeas (10 ^ 12) 12263)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12263) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12263 t
    (oddRoot_row BstLean.Part267.row12263 (by norm_num) ⟨6131, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12265 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12265).prod (sampMeas (10 ^ 12) 12265)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12265) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12265 t
    (oddRoot_row BstLean.Part267.row12265 (by norm_num) ⟨6132, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12267 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12267).prod (sampMeas (10 ^ 12) 12267)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12267) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12267 t
    (oddRoot_row BstLean.Part267.row12267 (by norm_num) ⟨6133, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12269 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12269).prod (sampMeas (10 ^ 12) 12269)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12269) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12269 t
    (oddRoot_row BstLean.Part267.row12269 (by norm_num) ⟨6134, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12271 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12271).prod (sampMeas (10 ^ 12) 12271)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12271) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12271 t
    (oddRoot_row BstLean.Part267.row12271 (by norm_num) ⟨6135, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12273 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12273).prod (sampMeas (10 ^ 12) 12273)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12273) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12273 t
    (oddRoot_row BstLean.Part267.row12273 (by norm_num) ⟨6136, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12275 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12275).prod (sampMeas (10 ^ 12) 12275)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12275) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12275 t
    (oddRoot_row BstLean.Part267.row12275 (by norm_num) ⟨6137, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12277 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12277).prod (sampMeas (10 ^ 12) 12277)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12277) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12277 t
    (oddRoot_row BstLean.Part267.row12277 (by norm_num) ⟨6138, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12279 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12279).prod (sampMeas (10 ^ 12) 12279)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12279) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12279 t
    (oddRoot_row BstLean.Part267.row12279 (by norm_num) ⟨6139, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12281 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12281).prod (sampMeas (10 ^ 12) 12281)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12281) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12281 t
    (oddRoot_row BstLean.Part267.row12281 (by norm_num) ⟨6140, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12283 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12283).prod (sampMeas (10 ^ 12) 12283)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12283) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12283 t
    (oddRoot_row BstLean.Part267.row12283 (by norm_num) ⟨6141, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12285 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12285).prod (sampMeas (10 ^ 12) 12285)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12285) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12285 t
    (oddRoot_row BstLean.Part267.row12285 (by norm_num) ⟨6142, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12287 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12287).prod (sampMeas (10 ^ 12) 12287)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12287) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12287 t
    (oddRoot_row BstLean.Part267.row12287 (by norm_num) ⟨6143, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12289 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12289).prod (sampMeas (10 ^ 12) 12289)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12289) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12289 t
    (oddRoot_row BstLean.Part267.row12289 (by norm_num) ⟨6144, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12291 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12291).prod (sampMeas (10 ^ 12) 12291)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12291) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12291 t
    (oddRoot_row BstLean.Part267.row12291 (by norm_num) ⟨6145, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12293 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12293).prod (sampMeas (10 ^ 12) 12293)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12293) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12293 t
    (oddRoot_row BstLean.Part267.row12293 (by norm_num) ⟨6146, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12295 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12295).prod (sampMeas (10 ^ 12) 12295)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12295) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12295 t
    (oddRoot_row BstLean.Part267.row12295 (by norm_num) ⟨6147, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12297 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12297).prod (sampMeas (10 ^ 12) 12297)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12297) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12297 t
    (oddRoot_row BstLean.Part267.row12297 (by norm_num) ⟨6148, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12299 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12299).prod (sampMeas (10 ^ 12) 12299)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12299) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12299 t
    (oddRoot_row BstLean.Part267.row12299 (by norm_num) ⟨6149, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12301 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12301).prod (sampMeas (10 ^ 12) 12301)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12301) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12301 t
    (oddRoot_row BstLean.Part267.row12301 (by norm_num) ⟨6150, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12303 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12303).prod (sampMeas (10 ^ 12) 12303)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12303) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12303 t
    (oddRoot_row BstLean.Part267.row12303 (by norm_num) ⟨6151, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12305 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12305).prod (sampMeas (10 ^ 12) 12305)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12305) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12305 t
    (oddRoot_row BstLean.Part267.row12305 (by norm_num) ⟨6152, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12307 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12307).prod (sampMeas (10 ^ 12) 12307)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12307) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12307 t
    (oddRoot_row BstLean.Part267.row12307 (by norm_num) ⟨6153, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12309 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12309).prod (sampMeas (10 ^ 12) 12309)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12309) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12309 t
    (oddRoot_row BstLean.Part267.row12309 (by norm_num) ⟨6154, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12311 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12311).prod (sampMeas (10 ^ 12) 12311)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12311) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12311 t
    (oddRoot_row BstLean.Part267.row12311 (by norm_num) ⟨6155, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12313 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12313).prod (sampMeas (10 ^ 12) 12313)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12313) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12313 t
    (oddRoot_row BstLean.Part267.row12313 (by norm_num) ⟨6156, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12315 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12315).prod (sampMeas (10 ^ 12) 12315)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12315) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12315 t
    (oddRoot_row BstLean.Part267.row12315 (by norm_num) ⟨6157, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12317 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12317).prod (sampMeas (10 ^ 12) 12317)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12317) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12317 t
    (oddRoot_row BstLean.Part267.row12317 (by norm_num) ⟨6158, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12319 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12319).prod (sampMeas (10 ^ 12) 12319)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12319) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12319 t
    (oddRoot_row BstLean.Part267.row12319 (by norm_num) ⟨6159, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12321 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12321).prod (sampMeas (10 ^ 12) 12321)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12321) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12321 t
    (oddRoot_row BstLean.Part267.row12321 (by norm_num) ⟨6160, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12323 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12323).prod (sampMeas (10 ^ 12) 12323)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12323) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12323 t
    (oddRoot_row BstLean.Part267.row12323 (by norm_num) ⟨6161, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12325 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12325).prod (sampMeas (10 ^ 12) 12325)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12325) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12325 t
    (oddRoot_row BstLean.Part267.row12325 (by norm_num) ⟨6162, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12327 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12327).prod (sampMeas (10 ^ 12) 12327)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12327) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12327 t
    (oddRoot_row BstLean.Part267.row12327 (by norm_num) ⟨6163, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12329 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12329).prod (sampMeas (10 ^ 12) 12329)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12329) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12329 t
    (oddRoot_row BstLean.Part267.row12329 (by norm_num) ⟨6164, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12331 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12331).prod (sampMeas (10 ^ 12) 12331)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12331) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12331 t
    (oddRoot_row BstLean.Part267.row12331 (by norm_num) ⟨6165, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12333 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12333).prod (sampMeas (10 ^ 12) 12333)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12333) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12333 t
    (oddRoot_row BstLean.Part267.row12333 (by norm_num) ⟨6166, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12335 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12335).prod (sampMeas (10 ^ 12) 12335)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12335) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12335 t
    (oddRoot_row BstLean.Part267.row12335 (by norm_num) ⟨6167, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12337 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12337).prod (sampMeas (10 ^ 12) 12337)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12337) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12337 t
    (oddRoot_row BstLean.Part267.row12337 (by norm_num) ⟨6168, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12339 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12339).prod (sampMeas (10 ^ 12) 12339)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12339) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12339 t
    (oddRoot_row BstLean.Part267.row12339 (by norm_num) ⟨6169, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12341 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12341).prod (sampMeas (10 ^ 12) 12341)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12341) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12341 t
    (oddRoot_row BstLean.Part267.row12341 (by norm_num) ⟨6170, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12343 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12343).prod (sampMeas (10 ^ 12) 12343)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12343) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12343 t
    (oddRoot_row BstLean.Part267.row12343 (by norm_num) ⟨6171, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12345 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12345).prod (sampMeas (10 ^ 12) 12345)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12345) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12345 t
    (oddRoot_row BstLean.Part267.row12345 (by norm_num) ⟨6172, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12347 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12347).prod (sampMeas (10 ^ 12) 12347)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12347) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12347 t
    (oddRoot_row BstLean.Part267.row12347 (by norm_num) ⟨6173, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_12349 (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 12349).prod (sampMeas (10 ^ 12) 12349)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12349) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} :=
  classifier_from_row_st BstLean.Part267.row12349 t
    (oddRoot_row BstLean.Part267.row12349 (by norm_num) ⟨6174, by norm_num⟩ t
      (fun c hc => ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩))

theorem stated_odd_block_12225 (n : ℕ) (hl : 12225 ≤ n) (hu : n ≤ 12249) (ho : Odd n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  interval_cases n
  · exact stated_odd_12225 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12227 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12229 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12231 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12233 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12235 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12237 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12239 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12241 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12243 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12245 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12247 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12249 t

theorem stated_odd_block_12250 (n : ℕ) (hl : 12250 ≤ n) (hu : n ≤ 12274) (ho : Odd n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  interval_cases n
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12251 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12253 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12255 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12257 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12259 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12261 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12263 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12265 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12267 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12269 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12271 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12273 t
  · simp [Nat.odd_iff] at ho

theorem stated_odd_block_12275 (n : ℕ) (hl : 12275 ≤ n) (hu : n ≤ 12299) (ho : Odd n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  interval_cases n
  · exact stated_odd_12275 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12277 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12279 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12281 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12283 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12285 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12287 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12289 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12291 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12293 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12295 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12297 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12299 t

theorem stated_odd_block_12300 (n : ℕ) (hl : 12300 ≤ n) (hu : n ≤ 12324) (ho : Odd n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  interval_cases n
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12301 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12303 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12305 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12307 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12309 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12311 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12313 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12315 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12317 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12319 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12321 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12323 t
  · simp [Nat.odd_iff] at ho

theorem stated_odd_block_12325 (n : ℕ) (hl : 12325 ≤ n) (hu : n ≤ 12349) (ho : Odd n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  interval_cases n
  · exact stated_odd_12325 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12327 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12329 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12331 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12333 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12335 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12337 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12339 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12341 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12343 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12345 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12347 t
  · simp [Nat.odd_iff] at ho
  · exact stated_odd_12349 t

/-- **The 12 225–12 349 family for the stated program, odd and even.** -/
theorem classifier_stated_12225_12349 : ∀ n ∈ Set.Icc (12225 : ℕ) 12349, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  intro n hn t
  obtain ⟨hl, hu⟩ := hn
  rcases Nat.even_or_odd n with he | ho
  · rw [BstLean.Part272.statedDesign_even (by omega) he]
    exact BstLean.Part267.classifier_12225_12349 n ⟨hl, hu⟩ t
  · by_cases h1 : n ≤ 12249
    · exact stated_odd_block_12225 n hl h1 ho t
    by_cases h2 : n ≤ 12274
    · exact stated_odd_block_12250 n (by omega) h2 ho t
    by_cases h3 : n ≤ 12299
    · exact stated_odd_block_12275 n (by omega) h3 ho t
    by_cases h4 : n ≤ 12324
    · exact stated_odd_block_12300 n (by omega) h4 ho t
    exact stated_odd_block_12325 n (by omega) hu ho t

end BstLean.Part278
