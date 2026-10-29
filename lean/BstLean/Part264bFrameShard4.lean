import BstLean.Part264bFrames4
namespace BstLean.Part264b
open Set
noncomputable def frameShard4 (n : ℕ) (hn : n ∈ Icc 12325 12349) : FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12325.frameData12325
  · exact N12326.frameData12326
  · exact N12327.frameData12327
  · exact N12328.frameData12328
  · exact N12329.frameData12329
  · exact N12330.frameData12330
  · exact N12331.frameData12331
  · exact N12332.frameData12332
  · exact N12333.frameData12333
  · exact N12334.frameData12334
  · exact N12335.frameData12335
  · exact N12336.frameData12336
  · exact N12337.frameData12337
  · exact N12338.frameData12338
  · exact N12339.frameData12339
  · exact N12340.frameData12340
  · exact N12341.frameData12341
  · exact N12342.frameData12342
  · exact N12343.frameData12343
  · exact N12344.frameData12344
  · exact N12345.frameData12345
  · exact N12346.frameData12346
  · exact N12347.frameData12347
  · exact N12348.frameData12348
  · exact N12349.frameData12349
end BstLean.Part264b
