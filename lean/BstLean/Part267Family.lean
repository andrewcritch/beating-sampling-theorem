import BstLean.Part267Rows0
import BstLean.Part267Rows1
import BstLean.Part267Rows2
import BstLean.Part267Rows3
import BstLean.Part267Rows4
import BstLean.Part267Rows5

/-! All 125 complete rows give the unconditional interval classifier. -/
namespace BstLean.Part267
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part156
open BstLean.Part169 (paperDesignP)

noncomputable def familyInputs : BstLean.Part259.FamilyInputs (Icc 12225 12349) where
  row := by
    intro n hn
    obtain ⟨hl, hu⟩ := hn
    interval_cases n
    · exact row12225
    · exact row12226
    · exact row12227
    · exact row12228
    · exact row12229
    · exact row12230
    · exact row12231
    · exact row12232
    · exact row12233
    · exact row12234
    · exact row12235
    · exact row12236
    · exact row12237
    · exact row12238
    · exact row12239
    · exact row12240
    · exact row12241
    · exact row12242
    · exact row12243
    · exact row12244
    · exact row12245
    · exact row12246
    · exact row12247
    · exact row12248
    · exact row12249
    · exact row12250
    · exact row12251
    · exact row12252
    · exact row12253
    · exact row12254
    · exact row12255
    · exact row12256
    · exact row12257
    · exact row12258
    · exact row12259
    · exact row12260
    · exact row12261
    · exact row12262
    · exact row12263
    · exact row12264
    · exact row12265
    · exact row12266
    · exact row12267
    · exact row12268
    · exact row12269
    · exact row12270
    · exact row12271
    · exact row12272
    · exact row12273
    · exact row12274
    · exact row12275
    · exact row12276
    · exact row12277
    · exact row12278
    · exact row12279
    · exact row12280
    · exact row12281
    · exact row12282
    · exact row12283
    · exact row12284
    · exact row12285
    · exact row12286
    · exact row12287
    · exact row12288
    · exact row12289
    · exact row12290
    · exact row12291
    · exact row12292
    · exact row12293
    · exact row12294
    · exact row12295
    · exact row12296
    · exact row12297
    · exact row12298
    · exact row12299
    · exact row12300
    · exact row12301
    · exact row12302
    · exact row12303
    · exact row12304
    · exact row12305
    · exact row12306
    · exact row12307
    · exact row12308
    · exact row12309
    · exact row12310
    · exact row12311
    · exact row12312
    · exact row12313
    · exact row12314
    · exact row12315
    · exact row12316
    · exact row12317
    · exact row12318
    · exact row12319
    · exact row12320
    · exact row12321
    · exact row12322
    · exact row12323
    · exact row12324
    · exact row12325
    · exact row12326
    · exact row12327
    · exact row12328
    · exact row12329
    · exact row12330
    · exact row12331
    · exact row12332
    · exact row12333
    · exact row12334
    · exact row12335
    · exact row12336
    · exact row12337
    · exact row12338
    · exact row12339
    · exact row12340
    · exact row12341
    · exact row12342
    · exact row12343
    · exact row12344
    · exact row12345
    · exact row12346
    · exact row12347
    · exact row12348
    · exact row12349

theorem classifier_12225_12349 : ∀ n ∈ Set.Icc (12225 : ℕ) 12349, ∀ t : ℝ,
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10^12) x.1 x.2)} :=
  BstLean.Part259.classifier_on_set familyInputs

end BstLean.Part267
