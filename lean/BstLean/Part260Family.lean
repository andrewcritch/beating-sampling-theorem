import BstLean.Part260Data0
import BstLean.Part260Data1
import BstLean.Part260Data2
import BstLean.Part260Data3
import BstLean.Part260Data4
import BstLean.Part259Family

/-! Complete World supplies on the requested dimension set. Other RowInputs
fields remain separate obligations. Each parameter equals its Part259 row. -/
namespace BstLean.Part260
open Real MeasureTheory Set BstLean.Part130 BstLean.Part137 BstLean.Part157
open BstLean.Part159 BstLean.Part192 BstLean.Part227

noncomputable def worldParameters (n : ℕ) : WorldParameters :=
  if n = 12225 then Part259.world12225 else
  if n = 12226 then Part259.world12226 else
  if n = 12227 then Part259.world12227 else
  if n = 12228 then Part259.world12228 else
  if n = 12229 then Part259.world12229 else
  if n = 12230 then Part259.world12230 else
  if n = 12231 then Part259.world12231 else
  if n = 12232 then Part259.world12232 else
  if n = 12233 then Part259.world12233 else
  if n = 12234 then Part259.world12234 else
  if n = 12235 then Part259.world12235 else
  if n = 12236 then Part259.world12236 else
  if n = 12237 then Part259.world12237 else
  if n = 12238 then Part259.world12238 else
  if n = 12239 then Part259.world12239 else
  if n = 12240 then Part259.world12240 else
  if n = 12241 then Part259.world12241 else
  if n = 12242 then Part259.world12242 else
  if n = 12243 then Part259.world12243 else
  if n = 12244 then Part259.world12244 else
  if n = 12245 then Part259.world12245 else
  if n = 12246 then Part259.world12246 else
  if n = 12247 then Part259.world12247 else
  if n = 12248 then Part259.world12248 else
  if n = 12249 then Part259.world12249 else
  if n = 12250 then Part259.world12250 else
  if n = 12251 then Part259.world12251 else
  if n = 12252 then Part259.world12252 else
  if n = 12253 then Part259.world12253 else
  if n = 12254 then Part259.world12254 else
  if n = 12255 then Part259.world12255 else
  if n = 12256 then Part259.world12256 else
  if n = 12257 then Part259.world12257 else
  if n = 12258 then Part259.world12258 else
  if n = 12259 then Part259.world12259 else
  if n = 12260 then Part259.world12260 else
  if n = 12261 then Part259.world12261 else
  if n = 12262 then Part259.world12262 else
  if n = 12263 then Part259.world12263 else
  if n = 12264 then Part259.world12264 else
  if n = 12265 then Part259.world12265 else
  if n = 12266 then Part259.world12266 else
  if n = 12267 then Part259.world12267 else
  if n = 12268 then Part259.world12268 else
  if n = 12269 then Part259.world12269 else
  if n = 12270 then Part259.world12270 else
  if n = 12271 then Part259.world12271 else
  if n = 12272 then Part259.world12272 else
  if n = 12273 then Part259.world12273 else
  if n = 12274 then Part259.world12274 else
  if n = 12275 then Part259.world12275 else
  if n = 12276 then Part259.world12276 else
  if n = 12277 then Part259.world12277 else
  if n = 12278 then Part259.world12278 else
  if n = 12279 then Part259.world12279 else
  if n = 12280 then Part259.world12280 else
  if n = 12281 then Part259.world12281 else
  if n = 12282 then Part259.world12282 else
  if n = 12283 then Part259.world12283 else
  if n = 12284 then Part259.world12284 else
  if n = 12285 then Part259.world12285 else
  if n = 12286 then Part259.world12286 else
  if n = 12287 then Part259.world12287 else
  if n = 12288 then Part259.world12288 else
  if n = 12289 then Part259.world12289 else
  if n = 12290 then Part259.world12290 else
  if n = 12291 then Part259.world12291 else
  if n = 12292 then Part259.world12292 else
  if n = 12293 then Part259.world12293 else
  if n = 12294 then Part259.world12294 else
  if n = 12295 then Part259.world12295 else
  if n = 12296 then Part259.world12296 else
  if n = 12297 then Part259.world12297 else
  if n = 12298 then Part259.world12298 else
  if n = 12299 then Part259.world12299 else
  if n = 12300 then Part259.world12300 else
  if n = 12301 then Part259.world12301 else
  if n = 12302 then Part259.world12302 else
  if n = 12303 then Part259.world12303 else
  if n = 12304 then Part259.world12304 else
  if n = 12305 then Part259.world12305 else
  if n = 12306 then Part259.world12306 else
  if n = 12307 then Part259.world12307 else
  if n = 12308 then Part259.world12308 else
  if n = 12309 then Part259.world12309 else
  if n = 12310 then Part259.world12310 else
  if n = 12311 then Part259.world12311 else
  if n = 12312 then Part259.world12312 else
  if n = 12313 then Part259.world12313 else
  if n = 12314 then Part259.world12314 else
  if n = 12315 then Part259.world12315 else
  if n = 12316 then Part259.world12316 else
  if n = 12317 then Part259.world12317 else
  if n = 12318 then Part259.world12318 else
  if n = 12319 then Part259.world12319 else
  if n = 12320 then Part259.world12320 else
  if n = 12321 then Part259.world12321 else
  if n = 12322 then Part259.world12322 else
  if n = 12323 then Part259.world12323 else
  if n = 12324 then Part259.world12324 else
  if n = 12325 then Part259.world12325 else
  if n = 12326 then Part259.world12326 else
  if n = 12327 then Part259.world12327 else
  if n = 12328 then Part259.world12328 else
  if n = 12329 then Part259.world12329 else
  if n = 12330 then Part259.world12330 else
  if n = 12331 then Part259.world12331 else
  if n = 12332 then Part259.world12332 else
  if n = 12333 then Part259.world12333 else
  if n = 12334 then Part259.world12334 else
  if n = 12335 then Part259.world12335 else
  if n = 12336 then Part259.world12336 else
  if n = 12337 then Part259.world12337 else
  if n = 12338 then Part259.world12338 else
  if n = 12339 then Part259.world12339 else
  if n = 12340 then Part259.world12340 else
  if n = 12341 then Part259.world12341 else
  if n = 12342 then Part259.world12342 else
  if n = 12343 then Part259.world12343 else
  if n = 12344 then Part259.world12344 else
  if n = 12345 then Part259.world12345 else
  if n = 12346 then Part259.world12346 else
  if n = 12347 then Part259.world12347 else
  if n = 12348 then Part259.world12348 else
  Part259.world12349

theorem parameters12225 : worldParameters 12225 = Part259.world12225 := by
  norm_num [worldParameters]

theorem parameters12226 : worldParameters 12226 = Part259.world12226 := by
  norm_num [worldParameters]

theorem parameters12227 : worldParameters 12227 = Part259.world12227 := by
  norm_num [worldParameters]

theorem parameters12228 : worldParameters 12228 = Part259.world12228 := by
  norm_num [worldParameters]

theorem parameters12229 : worldParameters 12229 = Part259.world12229 := by
  norm_num [worldParameters]

theorem parameters12230 : worldParameters 12230 = Part259.world12230 := by
  norm_num [worldParameters]

theorem parameters12231 : worldParameters 12231 = Part259.world12231 := by
  norm_num [worldParameters]

theorem parameters12232 : worldParameters 12232 = Part259.world12232 := by
  norm_num [worldParameters]

theorem parameters12233 : worldParameters 12233 = Part259.world12233 := by
  norm_num [worldParameters]

theorem parameters12234 : worldParameters 12234 = Part259.world12234 := by
  norm_num [worldParameters]

theorem parameters12235 : worldParameters 12235 = Part259.world12235 := by
  norm_num [worldParameters]

theorem parameters12236 : worldParameters 12236 = Part259.world12236 := by
  norm_num [worldParameters]

theorem parameters12237 : worldParameters 12237 = Part259.world12237 := by
  norm_num [worldParameters]

theorem parameters12238 : worldParameters 12238 = Part259.world12238 := by
  norm_num [worldParameters]

theorem parameters12239 : worldParameters 12239 = Part259.world12239 := by
  norm_num [worldParameters]

theorem parameters12240 : worldParameters 12240 = Part259.world12240 := by
  norm_num [worldParameters]

theorem parameters12241 : worldParameters 12241 = Part259.world12241 := by
  norm_num [worldParameters]

theorem parameters12242 : worldParameters 12242 = Part259.world12242 := by
  norm_num [worldParameters]

theorem parameters12243 : worldParameters 12243 = Part259.world12243 := by
  norm_num [worldParameters]

theorem parameters12244 : worldParameters 12244 = Part259.world12244 := by
  norm_num [worldParameters]

theorem parameters12245 : worldParameters 12245 = Part259.world12245 := by
  norm_num [worldParameters]

theorem parameters12246 : worldParameters 12246 = Part259.world12246 := by
  norm_num [worldParameters]

theorem parameters12247 : worldParameters 12247 = Part259.world12247 := by
  norm_num [worldParameters]

theorem parameters12248 : worldParameters 12248 = Part259.world12248 := by
  norm_num [worldParameters]

theorem parameters12249 : worldParameters 12249 = Part259.world12249 := by
  norm_num [worldParameters]

theorem parameters12250 : worldParameters 12250 = Part259.world12250 := by
  norm_num [worldParameters]

theorem parameters12251 : worldParameters 12251 = Part259.world12251 := by
  norm_num [worldParameters]

theorem parameters12252 : worldParameters 12252 = Part259.world12252 := by
  norm_num [worldParameters]

theorem parameters12253 : worldParameters 12253 = Part259.world12253 := by
  norm_num [worldParameters]

theorem parameters12254 : worldParameters 12254 = Part259.world12254 := by
  norm_num [worldParameters]

theorem parameters12255 : worldParameters 12255 = Part259.world12255 := by
  norm_num [worldParameters]

theorem parameters12256 : worldParameters 12256 = Part259.world12256 := by
  norm_num [worldParameters]

theorem parameters12257 : worldParameters 12257 = Part259.world12257 := by
  norm_num [worldParameters]

theorem parameters12258 : worldParameters 12258 = Part259.world12258 := by
  norm_num [worldParameters]

theorem parameters12259 : worldParameters 12259 = Part259.world12259 := by
  norm_num [worldParameters]

theorem parameters12260 : worldParameters 12260 = Part259.world12260 := by
  norm_num [worldParameters]

theorem parameters12261 : worldParameters 12261 = Part259.world12261 := by
  norm_num [worldParameters]

theorem parameters12262 : worldParameters 12262 = Part259.world12262 := by
  norm_num [worldParameters]

theorem parameters12263 : worldParameters 12263 = Part259.world12263 := by
  norm_num [worldParameters]

theorem parameters12264 : worldParameters 12264 = Part259.world12264 := by
  norm_num [worldParameters]

theorem parameters12265 : worldParameters 12265 = Part259.world12265 := by
  norm_num [worldParameters]

theorem parameters12266 : worldParameters 12266 = Part259.world12266 := by
  norm_num [worldParameters]

theorem parameters12267 : worldParameters 12267 = Part259.world12267 := by
  norm_num [worldParameters]

theorem parameters12268 : worldParameters 12268 = Part259.world12268 := by
  norm_num [worldParameters]

theorem parameters12269 : worldParameters 12269 = Part259.world12269 := by
  norm_num [worldParameters]

theorem parameters12270 : worldParameters 12270 = Part259.world12270 := by
  norm_num [worldParameters]

theorem parameters12271 : worldParameters 12271 = Part259.world12271 := by
  norm_num [worldParameters]

theorem parameters12272 : worldParameters 12272 = Part259.world12272 := by
  norm_num [worldParameters]

theorem parameters12273 : worldParameters 12273 = Part259.world12273 := by
  norm_num [worldParameters]

theorem parameters12274 : worldParameters 12274 = Part259.world12274 := by
  norm_num [worldParameters]

theorem parameters12275 : worldParameters 12275 = Part259.world12275 := by
  norm_num [worldParameters]

theorem parameters12276 : worldParameters 12276 = Part259.world12276 := by
  norm_num [worldParameters]

theorem parameters12277 : worldParameters 12277 = Part259.world12277 := by
  norm_num [worldParameters]

theorem parameters12278 : worldParameters 12278 = Part259.world12278 := by
  norm_num [worldParameters]

theorem parameters12279 : worldParameters 12279 = Part259.world12279 := by
  norm_num [worldParameters]

theorem parameters12280 : worldParameters 12280 = Part259.world12280 := by
  norm_num [worldParameters]

theorem parameters12281 : worldParameters 12281 = Part259.world12281 := by
  norm_num [worldParameters]

theorem parameters12282 : worldParameters 12282 = Part259.world12282 := by
  norm_num [worldParameters]

theorem parameters12283 : worldParameters 12283 = Part259.world12283 := by
  norm_num [worldParameters]

theorem parameters12284 : worldParameters 12284 = Part259.world12284 := by
  norm_num [worldParameters]

theorem parameters12285 : worldParameters 12285 = Part259.world12285 := by
  norm_num [worldParameters]

theorem parameters12286 : worldParameters 12286 = Part259.world12286 := by
  norm_num [worldParameters]

theorem parameters12287 : worldParameters 12287 = Part259.world12287 := by
  norm_num [worldParameters]

theorem parameters12288 : worldParameters 12288 = Part259.world12288 := by
  norm_num [worldParameters]

theorem parameters12289 : worldParameters 12289 = Part259.world12289 := by
  norm_num [worldParameters]

theorem parameters12290 : worldParameters 12290 = Part259.world12290 := by
  norm_num [worldParameters]

theorem parameters12291 : worldParameters 12291 = Part259.world12291 := by
  norm_num [worldParameters]

theorem parameters12292 : worldParameters 12292 = Part259.world12292 := by
  norm_num [worldParameters]

theorem parameters12293 : worldParameters 12293 = Part259.world12293 := by
  norm_num [worldParameters]

theorem parameters12294 : worldParameters 12294 = Part259.world12294 := by
  norm_num [worldParameters]

theorem parameters12295 : worldParameters 12295 = Part259.world12295 := by
  norm_num [worldParameters]

theorem parameters12296 : worldParameters 12296 = Part259.world12296 := by
  norm_num [worldParameters]

theorem parameters12297 : worldParameters 12297 = Part259.world12297 := by
  norm_num [worldParameters]

theorem parameters12298 : worldParameters 12298 = Part259.world12298 := by
  norm_num [worldParameters]

theorem parameters12299 : worldParameters 12299 = Part259.world12299 := by
  norm_num [worldParameters]

theorem parameters12300 : worldParameters 12300 = Part259.world12300 := by
  norm_num [worldParameters]

theorem parameters12301 : worldParameters 12301 = Part259.world12301 := by
  norm_num [worldParameters]

theorem parameters12302 : worldParameters 12302 = Part259.world12302 := by
  norm_num [worldParameters]

theorem parameters12303 : worldParameters 12303 = Part259.world12303 := by
  norm_num [worldParameters]

theorem parameters12304 : worldParameters 12304 = Part259.world12304 := by
  norm_num [worldParameters]

theorem parameters12305 : worldParameters 12305 = Part259.world12305 := by
  norm_num [worldParameters]

theorem parameters12306 : worldParameters 12306 = Part259.world12306 := by
  norm_num [worldParameters]

theorem parameters12307 : worldParameters 12307 = Part259.world12307 := by
  norm_num [worldParameters]

theorem parameters12308 : worldParameters 12308 = Part259.world12308 := by
  norm_num [worldParameters]

theorem parameters12309 : worldParameters 12309 = Part259.world12309 := by
  norm_num [worldParameters]

theorem parameters12310 : worldParameters 12310 = Part259.world12310 := by
  norm_num [worldParameters]

theorem parameters12311 : worldParameters 12311 = Part259.world12311 := by
  norm_num [worldParameters]

theorem parameters12312 : worldParameters 12312 = Part259.world12312 := by
  norm_num [worldParameters]

theorem parameters12313 : worldParameters 12313 = Part259.world12313 := by
  norm_num [worldParameters]

theorem parameters12314 : worldParameters 12314 = Part259.world12314 := by
  norm_num [worldParameters]

theorem parameters12315 : worldParameters 12315 = Part259.world12315 := by
  norm_num [worldParameters]

theorem parameters12316 : worldParameters 12316 = Part259.world12316 := by
  norm_num [worldParameters]

theorem parameters12317 : worldParameters 12317 = Part259.world12317 := by
  norm_num [worldParameters]

theorem parameters12318 : worldParameters 12318 = Part259.world12318 := by
  norm_num [worldParameters]

theorem parameters12319 : worldParameters 12319 = Part259.world12319 := by
  norm_num [worldParameters]

theorem parameters12320 : worldParameters 12320 = Part259.world12320 := by
  norm_num [worldParameters]

theorem parameters12321 : worldParameters 12321 = Part259.world12321 := by
  norm_num [worldParameters]

theorem parameters12322 : worldParameters 12322 = Part259.world12322 := by
  norm_num [worldParameters]

theorem parameters12323 : worldParameters 12323 = Part259.world12323 := by
  norm_num [worldParameters]

theorem parameters12324 : worldParameters 12324 = Part259.world12324 := by
  norm_num [worldParameters]

theorem parameters12325 : worldParameters 12325 = Part259.world12325 := by
  norm_num [worldParameters]

theorem parameters12326 : worldParameters 12326 = Part259.world12326 := by
  norm_num [worldParameters]

theorem parameters12327 : worldParameters 12327 = Part259.world12327 := by
  norm_num [worldParameters]

theorem parameters12328 : worldParameters 12328 = Part259.world12328 := by
  norm_num [worldParameters]

theorem parameters12329 : worldParameters 12329 = Part259.world12329 := by
  norm_num [worldParameters]

theorem parameters12330 : worldParameters 12330 = Part259.world12330 := by
  norm_num [worldParameters]

theorem parameters12331 : worldParameters 12331 = Part259.world12331 := by
  norm_num [worldParameters]

theorem parameters12332 : worldParameters 12332 = Part259.world12332 := by
  norm_num [worldParameters]

theorem parameters12333 : worldParameters 12333 = Part259.world12333 := by
  norm_num [worldParameters]

theorem parameters12334 : worldParameters 12334 = Part259.world12334 := by
  norm_num [worldParameters]

theorem parameters12335 : worldParameters 12335 = Part259.world12335 := by
  norm_num [worldParameters]

theorem parameters12336 : worldParameters 12336 = Part259.world12336 := by
  norm_num [worldParameters]

theorem parameters12337 : worldParameters 12337 = Part259.world12337 := by
  norm_num [worldParameters]

theorem parameters12338 : worldParameters 12338 = Part259.world12338 := by
  norm_num [worldParameters]

theorem parameters12339 : worldParameters 12339 = Part259.world12339 := by
  norm_num [worldParameters]

theorem parameters12340 : worldParameters 12340 = Part259.world12340 := by
  norm_num [worldParameters]

theorem parameters12341 : worldParameters 12341 = Part259.world12341 := by
  norm_num [worldParameters]

theorem parameters12342 : worldParameters 12342 = Part259.world12342 := by
  norm_num [worldParameters]

theorem parameters12343 : worldParameters 12343 = Part259.world12343 := by
  norm_num [worldParameters]

theorem parameters12344 : worldParameters 12344 = Part259.world12344 := by
  norm_num [worldParameters]

theorem parameters12345 : worldParameters 12345 = Part259.world12345 := by
  norm_num [worldParameters]

theorem parameters12346 : worldParameters 12346 = Part259.world12346 := by
  norm_num [worldParameters]

theorem parameters12347 : worldParameters 12347 = Part259.world12347 := by
  norm_num [worldParameters]

theorem parameters12348 : worldParameters 12348 = Part259.world12348 := by
  norm_num [worldParameters]

theorem parameters12349 : worldParameters 12349 = Part259.world12349 := by
  norm_num [worldParameters]

/-- This function supplies the World field of each Part259.RowInputs. -/
noncomputable def worldPackage (n : ℕ) (hn : n ∈ Icc (12225 : ℕ) 12349) :
    WorldPackage (paperProgram n) (worldParameters n) := by
  obtain ⟨hl, hu⟩ := hn
  interval_cases n
  · rw [parameters12225]; exact Row12225.worldPackage
  · rw [parameters12226]; exact Row12226.worldPackage
  · rw [parameters12227]; exact Row12227.worldPackage
  · rw [parameters12228]; exact Row12228.worldPackage
  · rw [parameters12229]; exact Row12229.worldPackage
  · rw [parameters12230]; exact Row12230.worldPackage
  · rw [parameters12231]; exact Row12231.worldPackage
  · rw [parameters12232]; exact Row12232.worldPackage
  · rw [parameters12233]; exact Row12233.worldPackage
  · rw [parameters12234]; exact Row12234.worldPackage
  · rw [parameters12235]; exact Row12235.worldPackage
  · rw [parameters12236]; exact Row12236.worldPackage
  · rw [parameters12237]; exact Row12237.worldPackage
  · rw [parameters12238]; exact Row12238.worldPackage
  · rw [parameters12239]; exact Row12239.worldPackage
  · rw [parameters12240]; exact Row12240.worldPackage
  · rw [parameters12241]; exact Row12241.worldPackage
  · rw [parameters12242]; exact Row12242.worldPackage
  · rw [parameters12243]; exact Row12243.worldPackage
  · rw [parameters12244]; exact Row12244.worldPackage
  · rw [parameters12245]; exact Row12245.worldPackage
  · rw [parameters12246]; exact Row12246.worldPackage
  · rw [parameters12247]; exact Row12247.worldPackage
  · rw [parameters12248]; exact Row12248.worldPackage
  · rw [parameters12249]; exact Row12249.worldPackage
  · rw [parameters12250]; exact Row12250.worldPackage
  · rw [parameters12251]; exact Row12251.worldPackage
  · rw [parameters12252]; exact Row12252.worldPackage
  · rw [parameters12253]; exact Row12253.worldPackage
  · rw [parameters12254]; exact Row12254.worldPackage
  · rw [parameters12255]; exact Row12255.worldPackage
  · rw [parameters12256]; exact Row12256.worldPackage
  · rw [parameters12257]; exact Row12257.worldPackage
  · rw [parameters12258]; exact Row12258.worldPackage
  · rw [parameters12259]; exact Row12259.worldPackage
  · rw [parameters12260]; exact Row12260.worldPackage
  · rw [parameters12261]; exact Row12261.worldPackage
  · rw [parameters12262]; exact Row12262.worldPackage
  · rw [parameters12263]; exact Row12263.worldPackage
  · rw [parameters12264]; exact Row12264.worldPackage
  · rw [parameters12265]; exact Row12265.worldPackage
  · rw [parameters12266]; exact Row12266.worldPackage
  · rw [parameters12267]; exact Row12267.worldPackage
  · rw [parameters12268]; exact Row12268.worldPackage
  · rw [parameters12269]; exact Row12269.worldPackage
  · rw [parameters12270]; exact Row12270.worldPackage
  · rw [parameters12271]; exact Row12271.worldPackage
  · rw [parameters12272]; exact Row12272.worldPackage
  · rw [parameters12273]; exact Row12273.worldPackage
  · rw [parameters12274]; exact Row12274.worldPackage
  · rw [parameters12275]; exact Row12275.worldPackage
  · rw [parameters12276]; exact Row12276.worldPackage
  · rw [parameters12277]; exact Row12277.worldPackage
  · rw [parameters12278]; exact Row12278.worldPackage
  · rw [parameters12279]; exact Row12279.worldPackage
  · rw [parameters12280]; exact Row12280.worldPackage
  · rw [parameters12281]; exact Row12281.worldPackage
  · rw [parameters12282]; exact Row12282.worldPackage
  · rw [parameters12283]; exact Row12283.worldPackage
  · rw [parameters12284]; exact Row12284.worldPackage
  · rw [parameters12285]; exact Row12285.worldPackage
  · rw [parameters12286]; exact Row12286.worldPackage
  · rw [parameters12287]; exact Row12287.worldPackage
  · rw [parameters12288]; exact Row12288.worldPackage
  · rw [parameters12289]; exact Row12289.worldPackage
  · rw [parameters12290]; exact Row12290.worldPackage
  · rw [parameters12291]; exact Row12291.worldPackage
  · rw [parameters12292]; exact Row12292.worldPackage
  · rw [parameters12293]; exact Row12293.worldPackage
  · rw [parameters12294]; exact Row12294.worldPackage
  · rw [parameters12295]; exact Row12295.worldPackage
  · rw [parameters12296]; exact Row12296.worldPackage
  · rw [parameters12297]; exact Row12297.worldPackage
  · rw [parameters12298]; exact Row12298.worldPackage
  · rw [parameters12299]; exact Row12299.worldPackage
  · rw [parameters12300]; exact Row12300.worldPackage
  · rw [parameters12301]; exact Row12301.worldPackage
  · rw [parameters12302]; exact Row12302.worldPackage
  · rw [parameters12303]; exact Row12303.worldPackage
  · rw [parameters12304]; exact Row12304.worldPackage
  · rw [parameters12305]; exact Row12305.worldPackage
  · rw [parameters12306]; exact Row12306.worldPackage
  · rw [parameters12307]; exact Row12307.worldPackage
  · rw [parameters12308]; exact Row12308.worldPackage
  · rw [parameters12309]; exact Row12309.worldPackage
  · rw [parameters12310]; exact Row12310.worldPackage
  · rw [parameters12311]; exact Row12311.worldPackage
  · rw [parameters12312]; exact Row12312.worldPackage
  · rw [parameters12313]; exact Row12313.worldPackage
  · rw [parameters12314]; exact Row12314.worldPackage
  · rw [parameters12315]; exact Row12315.worldPackage
  · rw [parameters12316]; exact Row12316.worldPackage
  · rw [parameters12317]; exact Row12317.worldPackage
  · rw [parameters12318]; exact Row12318.worldPackage
  · rw [parameters12319]; exact Row12319.worldPackage
  · rw [parameters12320]; exact Row12320.worldPackage
  · rw [parameters12321]; exact Row12321.worldPackage
  · rw [parameters12322]; exact Row12322.worldPackage
  · rw [parameters12323]; exact Row12323.worldPackage
  · rw [parameters12324]; exact Row12324.worldPackage
  · rw [parameters12325]; exact Row12325.worldPackage
  · rw [parameters12326]; exact Row12326.worldPackage
  · rw [parameters12327]; exact Row12327.worldPackage
  · rw [parameters12328]; exact Row12328.worldPackage
  · rw [parameters12329]; exact Row12329.worldPackage
  · rw [parameters12330]; exact Row12330.worldPackage
  · rw [parameters12331]; exact Row12331.worldPackage
  · rw [parameters12332]; exact Row12332.worldPackage
  · rw [parameters12333]; exact Row12333.worldPackage
  · rw [parameters12334]; exact Row12334.worldPackage
  · rw [parameters12335]; exact Row12335.worldPackage
  · rw [parameters12336]; exact Row12336.worldPackage
  · rw [parameters12337]; exact Row12337.worldPackage
  · rw [parameters12338]; exact Row12338.worldPackage
  · rw [parameters12339]; exact Row12339.worldPackage
  · rw [parameters12340]; exact Row12340.worldPackage
  · rw [parameters12341]; exact Row12341.worldPackage
  · rw [parameters12342]; exact Row12342.worldPackage
  · rw [parameters12343]; exact Row12343.worldPackage
  · rw [parameters12344]; exact Row12344.worldPackage
  · rw [parameters12345]; exact Row12345.worldPackage
  · rw [parameters12346]; exact Row12346.worldPackage
  · rw [parameters12347]; exact Row12347.worldPackage
  · rw [parameters12348]; exact Row12348.worldPackage
  · rw [parameters12349]; exact Row12349.worldPackage

theorem world_package_coverage : ∀ n ∈ Icc (12225 : ℕ) 12349,
    Nonempty (WorldPackage (paperProgram n) (worldParameters n)) :=
  fun n hn => ⟨worldPackage n hn⟩

noncomputable def actualNoiseInterval (n : ℕ) : Set ℝ :=
  Icc (noiseLower (202225/100000)) (noiseUpper n (202831/100000))
/-- The finite family retains the exact hidden event and angle events. -/
theorem hidden_identity (n : ℕ) (hn : n ∈ Icc (12225 : ℕ) 12349) :
    (worldPackage n hn).hidden = hidden n (44945/10^6) (4/10000)
      (712/10000) (178/10^8) (1232/10^7) := by
  obtain ⟨hl, hu⟩ := hn
  interval_cases n <;> rfl

theorem angle_events (n : ℕ) (hn : n ∈ Icc (12225 : ℕ) 12349) :
    (worldPackage n hn).lowerEvent = Ethm (paperProgram n).design.toCentres ∧
    (worldPackage n hn).upperEvent = Ethp (paperProgram n).design.toCentres := by
  obtain ⟨hl, hu⟩ := hn
  interval_cases n <;> exact ⟨rfl, rfl⟩

/-- The analytic World source supplies the widened actual noise interval. -/
theorem actual_noise_window (n : ℕ) (hn : n ∈ Icc (12225 : ℕ) 12349)
    (c : Ret n) (hc : c ∈ Hof (worldPackage n hn).hidden ∩
      ((worldPackage n hn).lowerEvent ∩ (worldPackage n hn).upperEvent)) :
    BstLean.Part150.thetaC c.1.2 ((paperProgram n).design.tau0 c) ∈
      actualNoiseInterval n := by
  rw [hidden_identity n hn, (angle_events n hn).1, (angle_events n hn).2] at hc
  have hg : c.1.1 ∈ hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7) := hc.1
  have hdim : 4096 ≤ n := by have := hn.1; omega
  have hlo : (202225/100000 : ℝ) ≤ productLower n (1232/10^7) := by
    obtain ⟨hl, hu⟩ := hn
    interval_cases n
    · exact Row12225.product_lower
    · exact Row12226.product_lower
    · exact Row12227.product_lower
    · exact Row12228.product_lower
    · exact Row12229.product_lower
    · exact Row12230.product_lower
    · exact Row12231.product_lower
    · exact Row12232.product_lower
    · exact Row12233.product_lower
    · exact Row12234.product_lower
    · exact Row12235.product_lower
    · exact Row12236.product_lower
    · exact Row12237.product_lower
    · exact Row12238.product_lower
    · exact Row12239.product_lower
    · exact Row12240.product_lower
    · exact Row12241.product_lower
    · exact Row12242.product_lower
    · exact Row12243.product_lower
    · exact Row12244.product_lower
    · exact Row12245.product_lower
    · exact Row12246.product_lower
    · exact Row12247.product_lower
    · exact Row12248.product_lower
    · exact Row12249.product_lower
    · exact Row12250.product_lower
    · exact Row12251.product_lower
    · exact Row12252.product_lower
    · exact Row12253.product_lower
    · exact Row12254.product_lower
    · exact Row12255.product_lower
    · exact Row12256.product_lower
    · exact Row12257.product_lower
    · exact Row12258.product_lower
    · exact Row12259.product_lower
    · exact Row12260.product_lower
    · exact Row12261.product_lower
    · exact Row12262.product_lower
    · exact Row12263.product_lower
    · exact Row12264.product_lower
    · exact Row12265.product_lower
    · exact Row12266.product_lower
    · exact Row12267.product_lower
    · exact Row12268.product_lower
    · exact Row12269.product_lower
    · exact Row12270.product_lower
    · exact Row12271.product_lower
    · exact Row12272.product_lower
    · exact Row12273.product_lower
    · exact Row12274.product_lower
    · exact Row12275.product_lower
    · exact Row12276.product_lower
    · exact Row12277.product_lower
    · exact Row12278.product_lower
    · exact Row12279.product_lower
    · exact Row12280.product_lower
    · exact Row12281.product_lower
    · exact Row12282.product_lower
    · exact Row12283.product_lower
    · exact Row12284.product_lower
    · exact Row12285.product_lower
    · exact Row12286.product_lower
    · exact Row12287.product_lower
    · exact Row12288.product_lower
    · exact Row12289.product_lower
    · exact Row12290.product_lower
    · exact Row12291.product_lower
    · exact Row12292.product_lower
    · exact Row12293.product_lower
    · exact Row12294.product_lower
    · exact Row12295.product_lower
    · exact Row12296.product_lower
    · exact Row12297.product_lower
    · exact Row12298.product_lower
    · exact Row12299.product_lower
    · exact Row12300.product_lower
    · exact Row12301.product_lower
    · exact Row12302.product_lower
    · exact Row12303.product_lower
    · exact Row12304.product_lower
    · exact Row12305.product_lower
    · exact Row12306.product_lower
    · exact Row12307.product_lower
    · exact Row12308.product_lower
    · exact Row12309.product_lower
    · exact Row12310.product_lower
    · exact Row12311.product_lower
    · exact Row12312.product_lower
    · exact Row12313.product_lower
    · exact Row12314.product_lower
    · exact Row12315.product_lower
    · exact Row12316.product_lower
    · exact Row12317.product_lower
    · exact Row12318.product_lower
    · exact Row12319.product_lower
    · exact Row12320.product_lower
    · exact Row12321.product_lower
    · exact Row12322.product_lower
    · exact Row12323.product_lower
    · exact Row12324.product_lower
    · exact Row12325.product_lower
    · exact Row12326.product_lower
    · exact Row12327.product_lower
    · exact Row12328.product_lower
    · exact Row12329.product_lower
    · exact Row12330.product_lower
    · exact Row12331.product_lower
    · exact Row12332.product_lower
    · exact Row12333.product_lower
    · exact Row12334.product_lower
    · exact Row12335.product_lower
    · exact Row12336.product_lower
    · exact Row12337.product_lower
    · exact Row12338.product_lower
    · exact Row12339.product_lower
    · exact Row12340.product_lower
    · exact Row12341.product_lower
    · exact Row12342.product_lower
    · exact Row12343.product_lower
    · exact Row12344.product_lower
    · exact Row12345.product_lower
    · exact Row12346.product_lower
    · exact Row12347.product_lower
    · exact Row12348.product_lower
    · exact Row12349.product_lower
  have hhi : productUpper n (1232/10^7) ≤ (202831/100000 : ℝ) := by
    obtain ⟨hl, hu⟩ := hn
    interval_cases n
    · exact Row12225.producthi.2.trans (by norm_num)
    · exact Row12226.producthi.2.trans (by norm_num)
    · exact Row12227.producthi.2.trans (by norm_num)
    · exact Row12228.producthi.2.trans (by norm_num)
    · exact Row12229.producthi.2.trans (by norm_num)
    · exact Row12230.producthi.2.trans (by norm_num)
    · exact Row12231.producthi.2.trans (by norm_num)
    · exact Row12232.producthi.2.trans (by norm_num)
    · exact Row12233.producthi.2.trans (by norm_num)
    · exact Row12234.producthi.2.trans (by norm_num)
    · exact Row12235.producthi.2.trans (by norm_num)
    · exact Row12236.producthi.2.trans (by norm_num)
    · exact Row12237.producthi.2.trans (by norm_num)
    · exact Row12238.producthi.2.trans (by norm_num)
    · exact Row12239.producthi.2.trans (by norm_num)
    · exact Row12240.producthi.2.trans (by norm_num)
    · exact Row12241.producthi.2.trans (by norm_num)
    · exact Row12242.producthi.2.trans (by norm_num)
    · exact Row12243.producthi.2.trans (by norm_num)
    · exact Row12244.producthi.2.trans (by norm_num)
    · exact Row12245.producthi.2.trans (by norm_num)
    · exact Row12246.producthi.2.trans (by norm_num)
    · exact Row12247.producthi.2.trans (by norm_num)
    · exact Row12248.producthi.2.trans (by norm_num)
    · exact Row12249.producthi.2.trans (by norm_num)
    · exact Row12250.producthi.2.trans (by norm_num)
    · exact Row12251.producthi.2.trans (by norm_num)
    · exact Row12252.producthi.2.trans (by norm_num)
    · exact Row12253.producthi.2.trans (by norm_num)
    · exact Row12254.producthi.2.trans (by norm_num)
    · exact Row12255.producthi.2.trans (by norm_num)
    · exact Row12256.producthi.2.trans (by norm_num)
    · exact Row12257.producthi.2.trans (by norm_num)
    · exact Row12258.producthi.2.trans (by norm_num)
    · exact Row12259.producthi.2.trans (by norm_num)
    · exact Row12260.producthi.2.trans (by norm_num)
    · exact Row12261.producthi.2.trans (by norm_num)
    · exact Row12262.producthi.2.trans (by norm_num)
    · exact Row12263.producthi.2.trans (by norm_num)
    · exact Row12264.producthi.2.trans (by norm_num)
    · exact Row12265.producthi.2.trans (by norm_num)
    · exact Row12266.producthi.2.trans (by norm_num)
    · exact Row12267.producthi.2.trans (by norm_num)
    · exact Row12268.producthi.2.trans (by norm_num)
    · exact Row12269.producthi.2.trans (by norm_num)
    · exact Row12270.producthi.2.trans (by norm_num)
    · exact Row12271.producthi.2.trans (by norm_num)
    · exact Row12272.producthi.2.trans (by norm_num)
    · exact Row12273.producthi.2.trans (by norm_num)
    · exact Row12274.producthi.2.trans (by norm_num)
    · exact Row12275.producthi.2.trans (by norm_num)
    · exact Row12276.producthi.2.trans (by norm_num)
    · exact Row12277.producthi.2.trans (by norm_num)
    · exact Row12278.producthi.2.trans (by norm_num)
    · exact Row12279.producthi.2.trans (by norm_num)
    · exact Row12280.producthi.2.trans (by norm_num)
    · exact Row12281.producthi.2.trans (by norm_num)
    · exact Row12282.producthi.2.trans (by norm_num)
    · exact Row12283.producthi.2.trans (by norm_num)
    · exact Row12284.producthi.2.trans (by norm_num)
    · exact Row12285.producthi.2.trans (by norm_num)
    · exact Row12286.producthi.2.trans (by norm_num)
    · exact Row12287.producthi.2.trans (by norm_num)
    · exact Row12288.producthi.2.trans (by norm_num)
    · exact Row12289.producthi.2.trans (by norm_num)
    · exact Row12290.producthi.2.trans (by norm_num)
    · exact Row12291.producthi.2.trans (by norm_num)
    · exact Row12292.producthi.2.trans (by norm_num)
    · exact Row12293.producthi.2.trans (by norm_num)
    · exact Row12294.producthi.2.trans (by norm_num)
    · exact Row12295.producthi.2.trans (by norm_num)
    · exact Row12296.producthi.2.trans (by norm_num)
    · exact Row12297.producthi.2.trans (by norm_num)
    · exact Row12298.producthi.2.trans (by norm_num)
    · exact Row12299.producthi.2.trans (by norm_num)
    · exact Row12300.producthi.2.trans (by norm_num)
    · exact Row12301.producthi.2.trans (by norm_num)
    · exact Row12302.producthi.2.trans (by norm_num)
    · exact Row12303.producthi.2.trans (by norm_num)
    · exact Row12304.producthi.2.trans (by norm_num)
    · exact Row12305.producthi.2.trans (by norm_num)
    · exact Row12306.producthi.2.trans (by norm_num)
    · exact Row12307.producthi.2.trans (by norm_num)
    · exact Row12308.producthi.2.trans (by norm_num)
    · exact Row12309.producthi.2.trans (by norm_num)
    · exact Row12310.producthi.2.trans (by norm_num)
    · exact Row12311.producthi.2.trans (by norm_num)
    · exact Row12312.producthi.2.trans (by norm_num)
    · exact Row12313.producthi.2.trans (by norm_num)
    · exact Row12314.producthi.2.trans (by norm_num)
    · exact Row12315.producthi.2.trans (by norm_num)
    · exact Row12316.producthi.2.trans (by norm_num)
    · exact Row12317.producthi.2.trans (by norm_num)
    · exact Row12318.producthi.2.trans (by norm_num)
    · exact Row12319.producthi.2.trans (by norm_num)
    · exact Row12320.producthi.2.trans (by norm_num)
    · exact Row12321.producthi.2.trans (by norm_num)
    · exact Row12322.producthi.2.trans (by norm_num)
    · exact Row12323.producthi.2.trans (by norm_num)
    · exact Row12324.producthi.2.trans (by norm_num)
    · exact Row12325.producthi.2.trans (by norm_num)
    · exact Row12326.producthi.2.trans (by norm_num)
    · exact Row12327.producthi.2.trans (by norm_num)
    · exact Row12328.producthi.2.trans (by norm_num)
    · exact Row12329.producthi.2.trans (by norm_num)
    · exact Row12330.producthi.2.trans (by norm_num)
    · exact Row12331.producthi.2.trans (by norm_num)
    · exact Row12332.producthi.2.trans (by norm_num)
    · exact Row12333.producthi.2.trans (by norm_num)
    · exact Row12334.producthi.2.trans (by norm_num)
    · exact Row12335.producthi.2.trans (by norm_num)
    · exact Row12336.producthi.2.trans (by norm_num)
    · exact Row12337.producthi.2.trans (by norm_num)
    · exact Row12338.producthi.2.trans (by norm_num)
    · exact Row12339.producthi.2.trans (by norm_num)
    · exact Row12340.producthi.2.trans (by norm_num)
    · exact Row12341.producthi.2.trans (by norm_num)
    · exact Row12342.producthi.2.trans (by norm_num)
    · exact Row12343.producthi.2.trans (by norm_num)
    · exact Row12344.producthi.2.trans (by norm_num)
    · exact Row12345.producthi.2.trans (by norm_num)
    · exact Row12346.producthi.2.trans (by norm_num)
    · exact Row12347.producthi.2.trans (by norm_num)
    · exact Row12348.producthi.2.trans (by norm_num)
    · exact Row12349.producthi.2.trans (by norm_num)
  exact BstLean.Part227.noise_window hdim (paperProgram n).design rfl (fun _ => rfl)
    hg.2 hg.1.1.2 hg.1.2
    (window_guards (eB := 1232/10^7) hdim (by norm_num)).1
    (window_guards (eB := 1232/10^7) hdim (by norm_num)).2.1.le
    (window_guards (eB := 1232/10^7) hdim (by norm_num)).2.2
    (by norm_num) hlo hhi hc.2.1 hc.2.2

theorem actual_noise_enclosure (n : ℕ) (hn : n ∈ Icc (12225 : ℕ) 12349) :
    actualNoiseInterval n ⊆ Icc (46/100 : ℝ) (54/100) := by
  intro x hx
  obtain ⟨hl, hu⟩ := hn
  interval_cases n
  · exact ⟨(Row12225.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12225.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12226.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12226.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12227.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12227.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12228.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12228.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12229.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12229.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12230.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12230.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12231.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12231.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12232.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12232.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12233.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12233.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12234.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12234.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12235.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12235.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12236.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12236.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12237.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12237.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12238.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12238.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12239.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12239.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12240.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12240.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12241.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12241.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12242.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12242.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12243.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12243.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12244.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12244.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12245.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12245.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12246.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12246.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12247.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12247.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12248.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12248.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12249.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12249.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12250.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12250.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12251.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12251.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12252.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12252.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12253.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12253.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12254.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12254.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12255.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12255.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12256.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12256.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12257.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12257.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12258.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12258.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12259.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12259.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12260.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12260.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12261.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12261.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12262.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12262.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12263.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12263.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12264.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12264.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12265.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12265.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12266.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12266.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12267.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12267.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12268.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12268.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12269.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12269.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12270.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12270.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12271.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12271.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12272.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12272.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12273.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12273.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12274.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12274.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12275.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12275.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12276.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12276.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12277.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12277.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12278.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12278.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12279.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12279.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12280.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12280.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12281.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12281.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12282.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12282.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12283.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12283.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12284.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12284.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12285.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12285.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12286.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12286.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12287.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12287.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12288.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12288.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12289.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12289.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12290.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12290.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12291.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12291.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12292.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12292.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12293.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12293.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12294.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12294.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12295.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12295.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12296.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12296.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12297.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12297.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12298.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12298.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12299.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12299.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12300.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12300.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12301.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12301.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12302.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12302.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12303.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12303.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12304.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12304.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12305.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12305.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12306.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12306.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12307.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12307.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12308.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12308.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12309.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12309.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12310.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12310.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12311.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12311.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12312.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12312.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12313.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12313.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12314.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12314.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12315.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12315.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12316.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12316.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12317.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12317.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12318.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12318.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12319.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12319.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12320.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12320.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12321.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12321.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12322.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12322.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12323.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12323.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12324.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12324.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12325.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12325.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12326.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12326.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12327.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12327.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12328.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12328.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12329.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12329.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12330.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12330.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12331.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12331.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12332.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12332.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12333.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12333.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12334.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12334.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12335.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12335.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12336.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12336.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12337.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12337.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12338.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12338.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12339.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12339.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12340.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12340.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12341.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12341.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12342.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12342.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12343.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12343.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12344.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12344.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12345.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12345.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12346.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12346.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12347.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12347.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12348.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12348.noisehi.2.trans (by norm_num))⟩
  · exact ⟨(Row12349.noiselo.1.trans' (by norm_num)).trans hx.1,
      hx.2.trans (Row12349.noisehi.2.trans (by norm_num))⟩

end BstLean.Part260
