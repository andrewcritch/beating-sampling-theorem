import BstLean.Part281CellData2

namespace BstLean.Part281
open Real BstLean.Part263

theorem cert11909_0 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (16817750726601 / 20000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (1184388284847 / 50000000000000 : ℝ))
      (E := (cell11909 ⟨0, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (16817750726601 / 20000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (1184388284847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_1 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (84053512590581 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (47375610259 / 2000000000000 : ℝ))
      (E := (cell11909 ⟨1, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (84053512590581 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (47375610259 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_2 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (84018296860081 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (473756896647 / 20000000000000 : ℝ))
      (E := (cell11909 ⟨2, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (84018296860081 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (473756896647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_3 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (16796621280833 / 20000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (14804928069 / 625000000000 : ℝ))
      (E := (cell11909 ⟨3, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (16796621280833 / 20000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (14804928069 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_4 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (8394794118569 / 10000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368792488779 / 100000000000000 : ℝ))
      (E := (cell11909 ⟨4, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (8394794118569 / 10000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368792488779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_5 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83912801167713 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (592199107127 / 25000000000000 : ℝ))
      (E := (cell11909 ⟨5, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83912801167713 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (592199107127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_6 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (41938843156743 / 50000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (4737600871 / 200000000000 : ℝ))
      (E := (cell11909 ⟨6, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (41938843156743 / 50000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (4737600871 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_7 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (20960649146613 / 25000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (473760880687 / 20000000000000 : ℝ))
      (E := (cell11909 ⟨7, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (20960649146613 / 25000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (473760880687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_8 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (20951882987563 / 25000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (592202099813 / 25000000000000 : ℝ))
      (E := (cell11909 ⟨8, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (20951882987563 / 25000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (592202099813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_9 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (41886246184357 / 50000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368812373879 / 100000000000000 : ℝ))
      (E := (cell11909 ⟨9, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (41886246184357 / 50000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368812373879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_10 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83737477805861 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368816335837 / 100000000000000 : ℝ))
      (E := (cell11909 ⟨10, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83737477805861 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368816335837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_11 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83702488225903 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (236882035137 / 10000000000000 : ℝ))
      (E := (cell11909 ⟨11, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83702488225903 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (236882035137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_12 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83667523593237 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (1184412156283 / 50000000000000 : ℝ))
      (E := (cell11909 ⟨12, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83667523593237 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (1184412156283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_13 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83632583872449 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (148051767821 / 6250000000000 : ℝ))
      (E := (cell11909 ⟨13, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83632583872449 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (148051767821 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_14 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83597669028309 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368832276591 / 100000000000000 : ℝ))
      (E := (cell11909 ⟨14, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83597669028309 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368832276591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_15 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83562779025773 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368836236117 / 100000000000000 : ℝ))
      (E := (cell11909 ⟨15, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83562779025773 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368836236117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_16 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83527913829979 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (296105028593 / 12500000000000 : ℝ))
      (E := (cell11909 ⟨16, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83527913829979 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (296105028593 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_17 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (10436634175781 / 12500000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (473768840623 / 20000000000000 : ℝ))
      (E := (cell11909 ⟨17, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (10436634175781 / 12500000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (473768840623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_18 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (1043228221501 / 1250000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368848223811 / 100000000000000 : ℝ))
      (E := (cell11909 ⟨18, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (1043228221501 / 1250000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368848223811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11909_19 : CellCertificate 11909 (28443702787473 / 312500000000000 : ℝ) (176378263567519 / 100000000000000000 : ℝ) (89317977679169 / 2500000000000000 : ℝ)
    (cell11909 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · norm_num [cell11909]
  · have h := gap_lower (n := 11909) (a := (83423466737157 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368852180771 / 100000000000000 : ℝ))
      (E := (cell11909 ⟨19, by decide⟩).energy) (xi := (89317977679169 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11909 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11909) (a := (83423466737157 / 100000000000000 : ℝ)) (b := (43301385979 / 25000000000000 : ℝ)) (q := (2368852180771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11909]

theorem cert11910_0 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (10511092053213 / 12500000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (148036128329 / 6250000000000 : ℝ))
      (E := (cell11910 ⟨0, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (10511092053213 / 12500000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (148036128329 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_1 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (42026747868393 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368582068893 / 100000000000000 : ℝ))
      (E := (cell11910 ⟨1, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (42026747868393 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368582068893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_2 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (10502285044911 / 12500000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (592146513677 / 25000000000000 : ℝ))
      (E := (cell11910 ⟨2, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (10502285044911 / 12500000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (592146513677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_3 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (8398309025587 / 10000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (18948720169 / 800000000000 : ℝ))
      (E := (cell11910 ⟨3, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (8398309025587 / 10000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (18948720169 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_4 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (41973962694697 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368593978297 / 100000000000000 : ℝ))
      (E := (cell11910 ⟨4, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (41973962694697 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368593978297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_5 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (16782557144583 / 20000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368597993947 / 100000000000000 : ℝ))
      (E := (cell11910 ⟨5, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (16782557144583 / 20000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368597993947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_6 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (41938835609843 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184300981029 / 50000000000000 : ℝ))
      (E := (cell11910 ⟨6, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (41938835609843 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184300981029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_7 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (41921290921577 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (236860594981 / 10000000000000 : ℝ))
      (E := (cell11910 ⟨7, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (41921290921577 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (236860594981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_8 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (83807517556957 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184304954203 / 50000000000000 : ℝ))
      (E := (cell11910 ⟨8, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (83807517556957 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184304954203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_9 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (83772478324927 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184306952277 / 50000000000000 : ℝ))
      (E := (cell11910 ⟨9, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (83772478324927 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184306952277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_10 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (83737464111087 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (18504827257 / 781250000000 : ℝ))
      (E := (cell11910 ⟨10, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (83737464111087 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (18504827257 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_11 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (2615702339989 / 3125000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184310934849 / 50000000000000 : ℝ))
      (E := (cell11910 ⟨11, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (2615702339989 / 3125000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184310934849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_12 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (83667510595009 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184312927487 / 50000000000000 : ℝ))
      (E := (cell11910 ⟨12, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (83667510595009 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (1184312927487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_13 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (16726514244351 / 20000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (74019681077 / 3125000000000 : ℝ))
      (E := (cell11910 ⟨13, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (16726514244351 / 20000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (74019681077 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_14 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (4179882836233 / 5000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368633811691 / 100000000000000 : ℝ))
      (E := (cell11910 ⟨14, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (4179882836233 / 5000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368633811691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_15 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (41781383534339 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368637797849 / 100000000000000 : ℝ))
      (E := (cell11910 ⟨15, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (41781383534339 / 50000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (2368637797849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_16 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (1670558044379 / 2000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (236864175987 / 10000000000000 : ℝ))
      (E := (cell11910 ⟨16, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (1670558044379 / 2000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (236864175987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_17 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (83493062140797 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (925252251 / 39062500000 : ℝ))
      (E := (cell11910 ⟨17, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (83493062140797 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (925252251 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_18 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (83458246799721 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (47372993923 / 2000000000000 : ℝ))
      (E := (cell11910 ⟨18, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (83458246799721 / 100000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (47372993923 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11910_19 : CellCertificate 11910 (910166870476799 / 10000000000000000 : ℝ) (1763634491174081 / 1000000000000000000 : ℝ) (178620555053773 / 5000000000000000 : ℝ)
    (cell11910 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · norm_num [cell11910]
  · have h := gap_lower (n := 11910) (a := (20855864040351 / 25000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (148040855193 / 6250000000000 : ℝ))
      (E := (cell11910 ⟨19, by decide⟩).energy) (xi := (178620555053773 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11910 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11910) (a := (20855864040351 / 25000000000000 : ℝ)) (b := (17319080641 / 10000000000000 : ℝ)) (q := (148040855193 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11910]

theorem cert11911_0 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (5255544951331 / 6250000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368379819351 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨0, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (5255544951331 / 6250000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368379819351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_1 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (84053478885837 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368383849781 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨1, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (84053478885837 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368383849781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_2 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (16803652772259 / 20000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368387793503 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨2, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (16803652772259 / 20000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368387793503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_3 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (20995768527583 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (473678355287 / 20000000000000 : ℝ))
      (E := (cell11911 ⟨3, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (20995768527583 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (473678355287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_4 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (2623372174869 / 3125000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368395750991 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨4, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (2623372174869 / 3125000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368395750991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_5 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (41956385140391 / 50000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184199863529 / 50000000000000 : ℝ))
      (E := (cell11911 ⟨5, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (41956385140391 / 50000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184199863529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_6 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (41938828064253 / 50000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (296050464283 / 12500000000000 : ℝ))
      (E := (cell11911 ⟨6, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (41938828064253 / 50000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (296050464283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_7 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (20960641775607 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (296050965247 / 12500000000000 : ℝ))
      (E := (cell11911 ⟨7, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (20960641775607 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (296050965247 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_8 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (8380750316619 / 10000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (473682340279 / 20000000000000 : ℝ))
      (E := (cell11911 ⟨8, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (8380750316619 / 10000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (473682340279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_9 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (83772464283623 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368415661301 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨9, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (83772464283623 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368415661301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_10 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (83737450418751 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184209834083 / 50000000000000 : ℝ))
      (E := (cell11911 ⟨10, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (83737450418751 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184209834083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_11 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (16740492307157 / 20000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (118421180719 / 5000000000000 : ℝ))
      (E := (cell11911 ⟨11, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (16740492307157 / 20000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (118421180719 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_12 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (83667497599127 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184213811939 / 50000000000000 : ℝ))
      (E := (cell11911 ⟨12, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (83667497599127 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184213811939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_13 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (20908139643341 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368431588447 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨13, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (20908139643341 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368431588447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_14 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (83597644423267 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368435573569 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨14, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (83597644423267 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368435573569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_15 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (16712551022759 / 20000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368439586497 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨15, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (16712551022759 / 20000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368439586497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_16 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (83527890610089 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368443518053 / 100000000000000 : ℝ))
      (E := (cell11911 ⟨16, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (83527890610089 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (2368443518053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_17 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (83493050877469 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184223774601 / 50000000000000 : ℝ))
      (E := (cell11911 ⟨17, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (83493050877469 / 100000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (1184223774601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_18 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (521613974259 / 625000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (296056439013 / 12500000000000 : ℝ))
      (E := (cell11911 ⟨18, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (521613974259 / 625000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (296056439013 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11911_19 : CellCertificate 11911 (455067628442517 / 5000000000000000 : ℝ) (440871592889233 / 250000000000000000 : ℝ) (22325644688879 / 625000000000000 : ℝ)
    (cell11911 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · norm_num [cell11911]
  · have h := gap_lower (n := 11911) (a := (20855861396921 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (473691094209 / 20000000000000 : ℝ))
      (E := (cell11911 ⟨19, by decide⟩).energy) (xi := (22325644688879 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11911 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11911) (a := (20855861396921 / 25000000000000 : ℝ)) (b := (173176071463 / 100000000000000 : ℝ)) (q := (473691094209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11911]

theorem cert11912_0 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (4204435100989 / 5000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368181867959 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨0, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (4204435100989 / 5000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368181867959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_1 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (10506682754717 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368185855613 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨1, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (10506682754717 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368185855613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_2 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (10502280920763 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (1184094907573 / 50000000000000 : ℝ))
      (E := (cell11912 ⟨2, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (10502280920763 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (1184094907573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_3 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (83983057967549 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (59204845369 / 2500000000000 : ℝ))
      (E := (cell11912 ⟨3, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (83983057967549 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (59204845369 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_4 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (20986973451233 / 25000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (473639561373 / 20000000000000 : ℝ))
      (E := (cell11912 ⟨4, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (20986973451233 / 25000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (473639561373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_5 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (2622273588791 / 3125000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368201801349 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨5, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (2622273588791 / 3125000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368201801349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_6 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (10484705129993 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (118410287499 / 5000000000000 : ℝ))
      (E := (cell11912 ⟨6, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (10484705129993 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (118410287499 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_7 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (20960638091069 / 25000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (1184104859967 / 50000000000000 : ℝ))
      (E := (cell11912 ⟨7, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (20960638091069 / 25000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (1184104859967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_8 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (1676149775559 / 2000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368213720317 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨8, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (1676149775559 / 2000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368213720317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_9 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (52357781403 / 62500000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368217702051 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨9, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (52357781403 / 62500000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368217702051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_10 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (1674748734577 / 2000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (1184110836827 / 50000000000000 : ℝ))
      (E := (cell11912 ⟨10, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (1674748734577 / 2000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (1184110836827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_11 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (41851224097157 / 50000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368225643393 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨11, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (41851224097157 / 50000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368225643393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_12 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (10458435575699 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368229619279 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨12, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (10458435575699 / 12500000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368229619279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_13 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (83632545927273 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368233609069 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨13, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (83632545927273 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368233609069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_14 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (83597632124131 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368237620269 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨14, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (83597632124131 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368237620269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_15 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (20890685790281 / 25000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (148015100129 / 6250000000000 : ℝ))
      (E := (cell11912 ⟨15, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (20890685790281 / 25000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (148015100129 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_16 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (83527879003393 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368245561389 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨16, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (83527879003393 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368245561389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_17 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (41746519808131 / 50000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (473649912609 / 20000000000000 : ℝ))
      (E := (cell11912 ⟨17, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (41746519808131 / 50000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (473649912609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_18 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (16691644993047 / 20000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368253555401 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨18, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (16691644993047 / 20000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368253555401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11912_19 : CellCertificate 11912 (182020729684507 / 2000000000000000 : ℝ) (1763338276817473 / 1000000000000000000 : ℝ) (357179525458467 / 10000000000000000 : ℝ)
    (cell11912 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · norm_num [cell11912]
  · have h := gap_lower (n := 11912) (a := (83423435015997 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368257486483 / 100000000000000 : ℝ))
      (E := (cell11912 ⟨19, by decide⟩).energy) (xi := (357179525458467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11912 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11912) (a := (83423435015997 / 100000000000000 : ℝ)) (b := (6926453563 / 4000000000000 : ℝ)) (q := (2368257486483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11912]

theorem cert11913_0 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (84088684821157 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1183992070687 / 50000000000000 : ℝ))
      (E := (cell11913 ⟨0, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (84088684821157 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1183992070687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_1 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (525334032453 / 625000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (473597628827 / 20000000000000 : ℝ))
      (E := (cell11913 ⟨1, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (525334032453 / 625000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (473597628827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_2 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (84018230873713 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (591998029911 / 25000000000000 : ℝ))
      (E := (cell11913 ⟨2, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (84018230873713 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (591998029911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_3 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (262447005711 / 312500000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (2367996078317 / 100000000000000 : ℝ))
      (E := (cell11913 ⟨3, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (262447005711 / 312500000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (2367996078317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_4 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (20986969504191 / 25000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (148000005507 / 6250000000000 : ℝ))
      (E := (cell11913 ⟨4, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (20986969504191 / 25000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (148000005507 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_5 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (16782547880901 / 20000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (59200101083 / 2500000000000 : ℝ))
      (E := (cell11913 ⟨5, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (16782547880901 / 20000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (59200101083 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_6 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83877625953999 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (296001008651 / 12500000000000 : ℝ))
      (E := (cell11913 ⟨6, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83877625953999 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (296001008651 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_7 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (16768507525739 / 20000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (236801200157 / 10000000000000 : ℝ))
      (E := (cell11913 ⟨7, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (16768507525739 / 20000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (236801200157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_8 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83807474392237 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184008011541 / 50000000000000 : ℝ))
      (E := (cell11913 ⟨8, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83807474392237 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184008011541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_9 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83772436208459 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184009984439 / 50000000000000 : ℝ))
      (E := (cell11913 ⟨9, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83772436208459 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184009984439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_10 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (41868711520693 / 50000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (148001497707 / 6250000000000 : ℝ))
      (E := (cell11913 ⟨10, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (41868711520693 / 50000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (148001497707 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_11 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83702434855233 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184013978371 / 50000000000000 : ℝ))
      (E := (cell11913 ⟨11, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83702434855233 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184013978371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_12 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (41833735807201 / 50000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184015978589 / 50000000000000 : ℝ))
      (E := (cell11913 ⟨12, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (41833735807201 / 50000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (1184015978589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_13 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83632533283483 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (473607182871 / 20000000000000 : ℝ))
      (E := (cell11913 ⟨13, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83632533283483 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (473607182871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_14 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (334390479309 / 400000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (2368039893753 / 100000000000000 : ℝ))
      (E := (cell11913 ⟨14, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (334390479309 / 400000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (2368039893753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_15 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83562731210663 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (473608768911 / 20000000000000 : ℝ))
      (E := (cell11913 ⟨15, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83562731210663 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (473608768911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_16 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83527867398863 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (592011957947 / 25000000000000 : ℝ))
      (E := (cell11913 ⟨16, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83527867398863 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (592011957947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_17 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (10436628544647 / 12500000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (37000810347 / 1562500000000 : ℝ))
      (E := (cell11913 ⟨17, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (10436628544647 / 12500000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (37000810347 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_18 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83458214051107 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (59201395651 / 2500000000000 : ℝ))
      (E := (cell11913 ⟨18, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83458214051107 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (59201395651 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11913_19 : CellCertificate 11913 (182014409017599 / 2000000000000000 : ℝ) (1763190206949437 / 1000000000000000000 : ℝ) (22321796338437 / 625000000000000 : ℝ)
    (cell11913 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · norm_num [cell11913]
  · have h := gap_lower (n := 11913) (a := (83423424446341 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (2368059787569 / 100000000000000 : ℝ))
      (E := (cell11913 ⟨19, by decide⟩).energy) (xi := (22321796338437 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11913 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11913) (a := (83423424446341 / 100000000000000 : ℝ)) (b := (34629321849 / 20000000000000 : ℝ)) (q := (2368059787569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11913]

theorem cert11914_0 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (5255541726589 / 6250000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367786697317 / 100000000000000 : ℝ))
      (E := (cell11914 ⟨0, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (5255541726589 / 6250000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367786697317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_1 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (84053428350069 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (295973832201 / 12500000000000 : ℝ))
      (E := (cell11914 ⟨1, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (84053428350069 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (295973832201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_2 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (84018214384121 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (591948662309 / 25000000000000 : ℝ))
      (E := (cell11914 ⟨2, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (84018214384121 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (591948662309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_3 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (20995756422561 / 25000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (18498426757 / 781250000000 : ℝ))
      (E := (cell11914 ⟨3, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (20995756422561 / 25000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (18498426757 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_4 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (10493482778913 / 12500000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (473560518947 / 20000000000000 : ℝ))
      (E := (cell11914 ⟨4, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (10493482778913 / 12500000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (473560518947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_5 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (83912723970361 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (94712265059 / 4000000000000 : ℝ))
      (E := (cell11914 ⟨5, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (83912723970361 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (94712265059 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_6 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (83877610870671 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367810556237 / 100000000000000 : ℝ))
      (E := (cell11914 ⟨6, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (83877610870671 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367810556237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_7 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (41921261447843 / 50000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (1183907283443 / 50000000000000 : ℝ))
      (E := (cell11914 ⟨7, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (41921261447843 / 50000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (1183907283443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_8 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (1676149200181 / 2000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367818551787 / 100000000000000 : ℝ))
      (E := (cell11914 ⟨8, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (1676149200181 / 2000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367818551787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_9 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (41886211087299 / 50000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (591955629929 / 25000000000000 : ℝ))
      (E := (cell11914 ⟨9, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (41886211087299 / 50000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (591955629929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_10 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (83737409356357 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (295978309899 / 12500000000000 : ℝ))
      (E := (cell11914 ⟨10, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (83737409356357 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (295978309899 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_11 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (83702421518543 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367830496453 / 100000000000000 : ℝ))
      (E := (cell11914 ⟨11, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (83702421518543 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367830496453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_12 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (41833729312779 / 50000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367834463581 / 100000000000000 : ℝ))
      (E := (cell11914 ⟨12, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (41833729312779 / 50000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367834463581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_13 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (83632520641993 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (473567689257 / 20000000000000 : ℝ))
      (E := (cell11914 ⟨13, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (83632520641993 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (473567689257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_14 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (5224850470789 / 6250000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367842452067 / 100000000000000 : ℝ))
      (E := (cell11914 ⟨14, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (5224850470789 / 6250000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367842452067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_15 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (20890679815603 / 25000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367846430109 / 100000000000000 : ℝ))
      (E := (cell11914 ⟨15, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (20890679815603 / 25000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (2367846430109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_16 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (83527855796499 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (473570077469 / 20000000000000 : ℝ))
      (E := (cell11914 ⟨16, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (83527855796499 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (473570077469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_17 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (83493017100211 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (73995449643 / 3125000000000 : ℝ))
      (E := (cell11914 ⟨17, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (83493017100211 / 100000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (73995449643 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_18 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (16691640627811 / 20000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (1183929162013 / 50000000000000 : ℝ))
      (E := (cell11914 ⟨18, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (16691640627811 / 20000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (1183929162013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11914_19 : CellCertificate 11914 (910040446880107 / 10000000000000000 : ℝ) (1763042161946559 / 1000000000000000000 : ℝ) (89279490722469 / 2500000000000000 : ℝ)
    (cell11914 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · norm_num [cell11914]
  · have h := gap_lower (n := 11914) (a := (20855853469679 / 25000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (1183931158071 / 50000000000000 : ℝ))
      (E := (cell11914 ⟨19, by decide⟩).energy) (xi := (89279490722469 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11914 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11914) (a := (20855853469679 / 25000000000000 : ℝ)) (b := (173131881973 / 100000000000000 : ℝ)) (q := (1183931158071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11914]

theorem cert11915_0 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (42044325216291 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367589478073 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨0, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (42044325216291 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367589478073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_1 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (84053411510503 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367593453777 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨1, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (84053411510503 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367593453777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_2 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (5251137368583 / 6250000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (295949682711 / 12500000000000 : ℝ))
      (E := (cell11915 ⟨2, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (5251137368583 / 6250000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (295949682711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_3 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41991504777861 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (295950174589 / 12500000000000 : ℝ))
      (E := (cell11915 ⟨3, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41991504777861 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (295950174589 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_4 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (83947846448551 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367605384549 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨4, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (83947846448551 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367605384549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_5 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41956354269439 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183804688659 / 50000000000000 : ℝ))
      (E := (cell11915 ⟨5, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41956354269439 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183804688659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_6 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (83877595789959 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367613384643 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨6, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (83877595789959 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367613384643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_7 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (655019595041 / 781250000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (591904339501 / 25000000000000 : ℝ))
      (E := (cell11915 ⟨7, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (655019595041 / 781250000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (591904339501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_8 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (20951861407097 / 25000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (473524261287 / 20000000000000 : ℝ))
      (E := (cell11915 ⟨8, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (20951861407097 / 25000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (473524261287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_9 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41886204071609 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367625296637 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨9, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41886204071609 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367625296637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_10 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (83737395673763 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367629279249 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨10, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (83737395673763 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367629279249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_11 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41851204092121 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (236763326253 / 10000000000000 : ℝ))
      (E := (cell11915 ⟨11, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41851204092121 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (236763326253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_12 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41833722819529 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367637254491 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨12, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41833722819529 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367637254491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_13 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (83632508002803 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183820602431 / 50000000000000 : ℝ))
      (E := (cell11915 ⟨13, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (83632508002803 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183820602431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_14 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (83597595240253 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (147977827323 / 6250000000000 : ℝ))
      (E := (cell11915 ⟨14, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (83597595240253 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (147977827323 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_15 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (8356270731637 / 10000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367649184523 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨15, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (8356270731637 / 10000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367649184523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_16 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (83527844196299 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367653169973 / 100000000000000 : ℝ))
      (E := (cell11915 ⟨16, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (83527844196299 / 100000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (2367653169973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_17 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41746502922683 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183828571077 / 50000000000000 : ℝ))
      (E := (cell11915 ⟨17, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41746502922683 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183828571077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_18 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41729096114539 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183830582821 / 50000000000000 : ℝ))
      (E := (cell11915 ⟨18, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41729096114539 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (1183830582821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11915_19 : CellCertificate 11915 (14218888340587 / 156250000000000 : ℝ) (1762894141802577 / 1000000000000000000 : ℝ) (178543594940679 / 5000000000000000 : ℝ)
    (cell11915 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · norm_num [cell11915]
  · have h := gap_lower (n := 11915) (a := (41711701656561 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (18497383831 / 781250000000 : ℝ))
      (E := (cell11915 ⟨19, by decide⟩).energy) (xi := (178543594940679 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11915 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11915) (a := (41711701656561 / 50000000000000 : ℝ)) (b := (86558578629 / 50000000000000 : ℝ)) (q := (18497383831 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11915]

theorem cert11916_0 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (84088633242629 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (591848135341 / 25000000000000 : ℝ))
      (E := (cell11916 ⟨0, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (84088633242629 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (591848135341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_1 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (84053394673781 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (473479294981 / 20000000000000 : ℝ))
      (E := (cell11916 ⟨1, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (84053394673781 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (473479294981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_2 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (84018181413333 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (59185012481 / 2500000000000 : ℝ))
      (E := (cell11916 ⟨2, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (84018181413333 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (59185012481 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_3 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (5248937088997 / 6250000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183702225779 / 50000000000000 : ℝ))
      (E := (cell11916 ⟨3, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (5248937088997 / 6250000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183702225779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_4 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (16789566133701 / 20000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (591852114389 / 25000000000000 : ℝ))
      (E := (cell11916 ⟨4, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (16789566133701 / 20000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (591852114389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_5 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (10489086638757 / 12500000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367412411519 / 100000000000000 : ℝ))
      (E := (cell11916 ⟨5, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (10489086638757 / 12500000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367412411519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_6 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (83877580711863 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (295927047607 / 12500000000000 : ℝ))
      (E := (cell11916 ⟨6, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (83877580711863 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (295927047607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_7 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (83842493437379 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (236742037493 / 10000000000000 : ℝ))
      (E := (cell11916 ⟨7, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (83842493437379 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (236742037493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_8 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (83807431250251 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (473484868987 / 20000000000000 : ℝ))
      (E := (cell11916 ⟨8, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (83807431250251 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (473484868987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_9 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (20943098528579 / 25000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (295928544697 / 12500000000000 : ℝ))
      (E := (cell11916 ⟨9, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (20943098528579 / 25000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (295928544697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_10 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (20934345498401 / 25000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183716152767 / 50000000000000 : ℝ))
      (E := (cell11916 ⟨10, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (20934345498401 / 25000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183716152767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_11 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (8370239485233 / 10000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367436312953 / 100000000000000 : ℝ))
      (E := (cell11916 ⟨11, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (8370239485233 / 10000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367436312953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_12 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (41833716327451 / 50000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (236744027191 / 10000000000000 : ℝ))
      (E := (cell11916 ⟨12, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (41833716327451 / 50000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (236744027191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_13 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (83632495365911 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367444248113 / 100000000000000 : ℝ))
      (E := (cell11916 ⟨13, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (83632495365911 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367444248113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_14 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (16719516590027 / 20000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183724124531 / 50000000000000 : ℝ))
      (E := (cell11916 ⟨14, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (16719516590027 / 20000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183724124531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_15 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (41781347686269 / 50000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183726111969 / 50000000000000 : ℝ))
      (E := (cell11916 ⟨15, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (41781347686269 / 50000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183726111969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_16 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (83527832598263 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183728118883 / 50000000000000 : ℝ))
      (E := (cell11916 ⟨16, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (83527832598263 / 100000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (1183728118883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_17 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (130457804051 / 156250000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367460181061 / 100000000000000 : ℝ))
      (E := (cell11916 ⟨17, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (130457804051 / 156250000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367460181061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_18 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (3338327252847 / 4000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (295933022059 / 12500000000000 : ℝ))
      (E := (cell11916 ⟨18, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (3338327252847 / 4000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (295933022059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11916_19 : CellCertificate 11916 (909977265839071 / 10000000000000000 : ℝ) (1762746146511229 / 1000000000000000000 : ℝ) (2231602639923 / 62500000000000 : ℝ)
    (cell11916 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · norm_num [cell11916]
  · have h := gap_lower (n := 11916) (a := (41711696374779 / 50000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367468172089 / 100000000000000 : ℝ))
      (E := (cell11916 ⟨19, by decide⟩).energy) (xi := (2231602639923 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11916 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11916) (a := (41711696374779 / 50000000000000 : ℝ)) (b := (173102435099 / 100000000000000 : ℝ)) (q := (2367468172089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11916]

theorem cert11917_0 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (42044308027783 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367195771759 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨0, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (42044308027783 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367195771759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_1 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (42026688919951 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (147949986171 / 6250000000000 : ℝ))
      (E := (cell11917 ⟨1, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (42026688919951 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (147949986171 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_2 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (16803632986427 / 20000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367203761897 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨2, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (16803632986427 / 20000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367203761897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_3 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83982977294933 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367207731649 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨3, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83982977294933 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367207731649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_4 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (16789562978233 / 20000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367211698139 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨4, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (16789562978233 / 20000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367211698139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_5 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (41956338841947 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367215729083 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨5, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (41956338841947 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367215729083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_6 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83877565636381 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367219660597 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨6, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83877565636381 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367219660597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_7 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (1048030983901 / 1250000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183611837773 / 50000000000000 : ℝ))
      (E := (cell11917 ⟨7, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (1048030983901 / 1250000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183611837773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_8 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (41903708437319 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (591806916823 / 25000000000000 : ℝ))
      (E := (cell11917 ⟨8, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (41903708437319 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (591806916823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_9 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (41886190043947 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183615822303 / 50000000000000 : ℝ))
      (E := (cell11917 ⟨9, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (41886190043947 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183615822303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_10 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83737368315877 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (473447123201 / 20000000000000 : ℝ))
      (E := (cell11917 ⟨10, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83737368315877 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (473447123201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_11 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (41851190761403 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (9468958359 / 400000000000 : ℝ))
      (E := (cell11917 ⟨11, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (41851190761403 / 50000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (9468958359 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_12 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83667419673089 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367243573843 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨12, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83667419673089 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367243573843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_13 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83632482731317 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183623788021 / 50000000000000 : ℝ))
      (E := (cell11917 ⟨13, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83632482731317 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183623788021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_14 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83597570662271 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367251545797 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨14, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83597570662271 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367251545797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_15 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83562683430913 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (236725549029 / 10000000000000 : ℝ))
      (E := (cell11917 ⟨15, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83562683430913 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (236725549029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_16 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83527821002391 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367259474541 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨16, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83527821002391 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367259474541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_17 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (5218311458877 / 6250000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183631723593 / 50000000000000 : ℝ))
      (E := (cell11917 ⟨17, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (5218311458877 / 6250000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183631723593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_18 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83458170415347 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183633736399 / 50000000000000 : ℝ))
      (E := (cell11917 ⟨18, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83458170415347 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (1183633736399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11917_19 : CellCertificate 11917 (909945683003311 / 10000000000000000 : ℝ) (881299088033129 / 500000000000000000 : ℝ) (178512830203541 / 5000000000000000 : ℝ)
    (cell11917 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · norm_num [cell11917]
  · have h := gap_lower (n := 11917) (a := (83423382188023 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367271441307 / 100000000000000 : ℝ))
      (E := (cell11917 ⟨19, by decide⟩).energy) (xi := (178512830203541 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11917 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11917) (a := (83423382188023 / 100000000000000 : ℝ)) (b := (34617543099 / 20000000000000 : ℝ)) (q := (2367271441307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11917]

theorem cert11918_0 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (8408859887139 / 10000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183499671207 / 50000000000000 : ℝ))
      (E := (cell11918 ⟨0, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (8408859887139 / 10000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183499671207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_1 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (16810672201773 / 20000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (473400661507 / 20000000000000 : ℝ))
      (E := (cell11918 ⟨1, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (16810672201773 / 20000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (473400661507 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_2 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (84018148453733 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183503653713 / 50000000000000 : ℝ))
      (E := (cell11918 ⟨2, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (84018148453733 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183503653713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_3 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (16796592233733 / 20000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183505647389 / 50000000000000 : ℝ))
      (E := (cell11918 ⟨3, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (16796592233733 / 20000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183505647389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_4 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (8394779911653 / 10000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (2367015221923 / 100000000000000 : ℝ))
      (E := (cell11918 ⟨4, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (8394779911653 / 10000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (2367015221923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_5 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (10489082782549 / 12500000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (2367019214343 / 100000000000000 : ℝ))
      (E := (cell11918 ⟨5, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (10489082782549 / 12500000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (2367019214343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_6 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (41938775281757 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591755805967 / 25000000000000 : ℝ))
      (E := (cell11918 ⟨6, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (41938775281757 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591755805967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_7 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (1676849279787 / 2000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (295878400247 / 12500000000000 : ℝ))
      (E := (cell11918 ⟨7, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (1676849279787 / 2000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (295878400247 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_8 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (20951850625387 / 25000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183515578849 / 50000000000000 : ℝ))
      (E := (cell11918 ⟨8, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (20951850625387 / 25000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183515578849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_9 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (83772366063949 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591758789433 / 25000000000000 : ℝ))
      (E := (cell11918 ⟨9, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (83772366063949 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591758789433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_10 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (83737354640583 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (2367039152713 / 100000000000000 : ℝ))
      (E := (cell11918 ⟨10, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (83737354640583 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (2367039152713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_11 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (83702368195671 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183521546461 / 50000000000000 : ℝ))
      (E := (cell11918 ⟨11, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (83702368195671 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183521546461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_12 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (41833703346809 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (473409420459 / 20000000000000 : ℝ))
      (E := (cell11918 ⟨12, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (41833703346809 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (473409420459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_13 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (83632470099021 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183525536303 / 50000000000000 : ℝ))
      (E := (cell11918 ⟨13, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (83632470099021 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (1183525536303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_14 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (83597558376659 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591763767333 / 25000000000000 : ℝ))
      (E := (cell11918 ⟨14, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (83597558376659 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591763767333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_15 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (83562671491497 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (47341180833 / 2000000000000 : ℝ))
      (E := (cell11918 ⟨15, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (83562671491497 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (47341180833 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_16 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (41763904704341 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (236706299649 / 10000000000000 : ℝ))
      (E := (cell11918 ⟨16, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (41763904704341 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (236706299649 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_17 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (83492972093543 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (295883374831 / 12500000000000 : ℝ))
      (E := (cell11918 ⟨17, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (83492972093543 / 100000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (295883374831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_18 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (10432269938949 / 12500000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (473414199297 / 20000000000000 : ℝ))
      (E := (cell11918 ⟨18, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (10432269938949 / 12500000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (473414199297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11918_19 : CellCertificate 11918 (181982821057797 / 2000000000000000 : ℝ) (881225115230703 / 500000000000000000 : ℝ) (178497451968903 / 5000000000000000 : ℝ)
    (cell11918 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · norm_num [cell11918]
  · have h := gap_lower (n := 11918) (a := (41711685814259 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591768749047 / 25000000000000 : ℝ))
      (E := (cell11918 ⟨19, by decide⟩).energy) (xi := (178497451968903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11918 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11918) (a := (41711685814259 / 50000000000000 : ℝ)) (b := (34614599689 / 20000000000000 : ℝ)) (q := (591768749047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11918]

theorem cert11919_0 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (42044290845051 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366803080179 / 100000000000000 : ℝ))
      (E := (cell11919 ⟨0, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (42044290845051 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366803080179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_1 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (8405334418067 / 10000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366807061301 / 100000000000000 : ℝ))
      (E := (cell11919 ⟨1, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (8405334418067 / 10000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366807061301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_2 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (5251133248633 / 6250000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (147925692379 / 6250000000000 : ℝ))
      (E := (cell11919 ⟨2, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (5251133248633 / 6250000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (147925692379 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_3 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (20995736261287 / 25000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366815025369 / 100000000000000 : ℝ))
      (E := (cell11919 ⟨3, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (20995736261287 / 25000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366815025369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_4 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (83947783344599 / 100000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (147926189307 / 6250000000000 : ℝ))
      (E := (cell11919 ⟨4, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (83947783344599 / 100000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (147926189307 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_5 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (1678252936791 / 2000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366822982971 / 100000000000000 : ℝ))
      (E := (cell11919 ⟨5, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (1678252936791 / 2000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366822982971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_6 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (4193876774663 / 5000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183413506407 / 50000000000000 : ℝ))
      (E := (cell11919 ⟨6, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (4193876774663 / 5000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183413506407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_7 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (83842449269187 / 100000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366830954223 / 100000000000000 : ℝ))
      (E := (cell11919 ⟨7, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (83842449269187 / 100000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (2366830954223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_8 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (83807388130981 / 100000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (473366986393 / 20000000000000 : ℝ))
      (E := (cell11919 ⟨8, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (83807388130981 / 100000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (473366986393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_9 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (41886176021241 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (591709738721 / 25000000000000 : ℝ))
      (E := (cell11919 ⟨9, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (41886176021241 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (591709738721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_10 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (41868670483861 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183421457829 / 50000000000000 : ℝ))
      (E := (cell11919 ⟨10, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (41868670483861 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183421457829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_11 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (41851177435461 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (47336937609 / 2000000000000 : ℝ))
      (E := (cell11919 ⟨11, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (41851177435461 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (47336937609 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_12 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (8366739371649 / 10000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (473370171453 / 20000000000000 : ℝ))
      (E := (cell11919 ⟨12, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (8366739371649 / 10000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (473370171453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_13 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (41816228734511 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183427426927 / 50000000000000 : ℝ))
      (E := (cell11919 ⟨13, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (41816228734511 / 50000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183427426927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_14 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (835975460933 / 1000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183429409833 / 50000000000000 : ℝ))
      (E := (cell11919 ⟨14, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (835975460933 / 1000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183429409833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_15 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (5222666222143 / 6250000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (147928926247 / 6250000000000 : ℝ))
      (E := (cell11919 ⟨15, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (5222666222143 / 6250000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (147928926247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_16 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (16705559563427 / 20000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183433401807 / 50000000000000 : ℝ))
      (E := (cell11919 ⟨16, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (16705559563427 / 20000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (1183433401807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_17 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (20873240211793 / 25000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (591717694333 / 25000000000000 : ℝ))
      (E := (cell11919 ⟨17, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (20873240211793 / 25000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (591717694333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_18 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (8345814860991 / 10000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (473374949507 / 20000000000000 : ℝ))
      (E := (cell11919 ⟨18, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (8345814860991 / 10000000000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (473374949507 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11919_19 : CellCertificate 11919 (909882532694789 / 10000000000000000 : ℝ) (1762302309690419 / 1000000000000000000 : ℝ) (22310259561131 / 625000000000000 : ℝ)
    (cell11919 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · norm_num [cell11919]
  · have h := gap_lower (n := 11919) (a := (260698003347 / 312500000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (236687872041 / 10000000000000 : ℝ))
      (E := (cell11919 ⟨19, by decide⟩).energy) (xi := (22310259561131 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11919 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11919) (a := (260698003347 / 312500000000 : ℝ)) (b := (173058283949 / 100000000000000 : ℝ)) (q := (236687872041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11919]

theorem cert11920_0 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (84088564511701 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366607100491 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨0, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (84088564511701 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366607100491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_1 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (16810665471063 / 20000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183305548891 / 50000000000000 : ℝ))
      (E := (cell11920 ⟨1, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (16810665471063 / 20000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183305548891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_2 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (84018115505317 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366615073817 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨2, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (84018115505317 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366615073817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_3 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83982928924379 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (295827387099 / 12500000000000 : ℝ))
      (E := (cell11920 ⟨3, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83982928924379 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (295827387099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_4 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83947767575373 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (473324612259 / 20000000000000 : ℝ))
      (E := (cell11920 ⟨4, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83947767575373 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (473324612259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_5 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (16782526284273 / 20000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366627034971 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨5, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (16782526284273 / 20000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366627034971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_6 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83877520425619 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183315513719 / 50000000000000 : ℝ))
      (E := (cell11920 ⟨6, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83877520425619 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183315513719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_7 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83842434551593 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366634990169 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨7, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83842434551593 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366634990169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_8 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (10475921720367 / 12500000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366638990099 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨8, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (10475921720367 / 12500000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366638990099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_9 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (20943084505873 / 25000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366642978137 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨9, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (20943084505873 / 25000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366642978137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_10 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (20934331824323 / 25000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183323481399 / 50000000000000 : ℝ))
      (E := (cell11920 ⟨10, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (20934331824323 / 25000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183323481399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_11 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83702341548559 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366650894361 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨11, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83702341548559 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366650894361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_12 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83667380741703 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183327448379 / 50000000000000 : ℝ))
      (E := (cell11920 ⟨12, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83667380741703 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (1183327448379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_13 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (2090811121033 / 2500000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (591664715441 / 25000000000000 : ℝ))
      (E := (cell11920 ⟨13, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (2090811121033 / 2500000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (591664715441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_14 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (2612422931631 / 3125000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (591665713713 / 25000000000000 : ℝ))
      (E := (cell11920 ⟨14, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (2612422931631 / 3125000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (591665713713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_15 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (16712529523857 / 20000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366666825199 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨15, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (16712529523857 / 20000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366666825199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_16 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (334111144911 / 400000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366670837823 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨16, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (334111144911 / 400000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366670837823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_17 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (41746474801459 / 50000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (59166869581 / 2500000000000 : ℝ))
      (E := (cell11920 ⟨17, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (41746474801459 / 50000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (59166869581 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_18 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83458137710301 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366678784091 / 100000000000000 : ℝ))
      (E := (cell11920 ⟨18, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83458137710301 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (2366678784091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11920_19 : CellCertificate 11920 (45492548260971 / 500000000000000 : ℝ) (440538603436761 / 250000000000000000 : ℝ) (89233351881549 / 2500000000000000 : ℝ)
    (cell11920 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · norm_num [cell11920]
  · have h := gap_lower (n := 11920) (a := (83423350515591 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (473336557693 / 20000000000000 : ℝ))
      (E := (cell11920 ⟨19, by decide⟩).energy) (xi := (89233351881549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11920 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11920) (a := (83423350515591 / 100000000000000 : ℝ)) (b := (173043572007 / 100000000000000 : ℝ)) (q := (473336557693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11920]

theorem cert11921_0 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (42044273668093 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183205701679 / 50000000000000 : ℝ))
      (E := (cell11921 ⟨0, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (42044273668093 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183205701679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_1 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (84053310532801 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366415359239 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨1, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (84053310532801 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366415359239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_2 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (84018099035301 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (591604838113 / 25000000000000 : ℝ))
      (E := (cell11921 ⟨2, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (84018099035301 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (591604838113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_3 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (2099572820159 / 2500000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183211667843 / 50000000000000 : ℝ))
      (E := (cell11921 ⟨3, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (2099572820159 / 2500000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183211667843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_4 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83947751808849 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366427319081 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨4, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83947751808849 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366427319081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_5 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (41956308002919 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183215656257 / 50000000000000 : ℝ))
      (E := (cell11921 ⟨5, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (41956308002919 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183215656257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_6 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (8387750536059 / 10000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (473287053549 / 20000000000000 : ℝ))
      (E := (cell11921 ⟨6, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (8387750536059 / 10000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (473287053549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_7 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (20960604959141 / 25000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (118321962597 / 5000000000000 : ℝ))
      (E := (cell11921 ⟨7, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (20960604959141 / 25000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (118321962597 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_8 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83807359397413 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (236644321629 / 10000000000000 : ℝ))
      (E := (cell11921 ⟨8, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83807359397413 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (236644321629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_9 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (41886162003489 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (473289445499 / 20000000000000 : ℝ))
      (E := (cell11921 ⟨9, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (41886162003489 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (473289445499 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_10 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83737313629293 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366451178231 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨10, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83737313629293 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366451178231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_11 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83702328228583 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183227596317 / 50000000000000 : ℝ))
      (E := (cell11921 ⟨11, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83702328228583 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183227596317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_12 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83667367769257 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366459162779 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨12, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83667367769257 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366459162779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_13 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83632432215913 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366463154367 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨13, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83632432215913 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366463154367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_14 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (41798760766667 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366467116847 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨14, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (41798760766667 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366467116847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_15 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83562635686489 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (295808889433 / 12500000000000 : ℝ))
      (E := (cell11921 ⟨15, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83562635686489 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (295808889433 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_16 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (41763887320263 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366475099123 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨16, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (41763887320263 / 50000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366475099123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_17 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (4174646918039 / 5000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366479074497 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨17, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (4174646918039 / 5000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366479074497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_18 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83458126812763 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183241524009 / 50000000000000 : ℝ))
      (E := (cell11921 ⟨18, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83458126812763 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (1183241524009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11921_19 : CellCertificate 11921 (454909701430787 / 5000000000000000 : ℝ) (1762006542625033 / 1000000000000000000 : ℝ) (356902667580351 / 10000000000000000 : ℝ)
    (cell11921 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · norm_num [cell11921]
  · have h := gap_lower (n := 11921) (a := (83423339962169 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366487025867 / 100000000000000 : ℝ))
      (E := (cell11921 ⟨19, by decide⟩).energy) (xi := (356902667580351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11921 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11921) (a := (83423339962169 / 100000000000000 : ℝ)) (b := (21628607827 / 12500000000000 : ℝ)) (q := (2366487025867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11921]

theorem cert11922_0 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (16817706032711 / 20000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366215931063 / 100000000000000 : ℝ))
      (E := (cell11922 ⟨0, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (16817706032711 / 20000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366215931063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_1 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (42026646856563 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (295777487927 / 12500000000000 : ℝ))
      (E := (cell11922 ⟨1, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (42026646856563 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (295777487927 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_2 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (84018082568079 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (147888991013 / 6250000000000 : ℝ))
      (E := (cell11922 ⟨2, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (84018082568079 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (147888991013 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_3 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83982896691089 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366227857629 / 100000000000000 : ℝ))
      (E := (cell11922 ⟨3, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83982896691089 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366227857629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_4 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (20986934011257 / 25000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (591557950567 / 25000000000000 : ℝ))
      (E := (cell11922 ⟨4, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (20986934011257 / 25000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (591557950567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_5 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (10489075074121 / 12500000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (5915589539 / 250000000000 : ℝ))
      (E := (cell11922 ⟨5, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (10489075074121 / 12500000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (5915589539 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_6 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83877490298173 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (473247958319 / 20000000000000 : ℝ))
      (E := (cell11922 ⟨6, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83877490298173 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (473247958319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_7 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (41921202562051 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366243797419 / 100000000000000 : ℝ))
      (E := (cell11922 ⟨7, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (41921202562051 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366243797419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_8 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (8380734503441 / 10000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (591561931589 / 25000000000000 : ℝ))
      (E := (cell11922 ⟨8, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (8380734503441 / 10000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (591561931589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_9 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83772309992939 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366251760891 / 100000000000000 : ℝ))
      (E := (cell11922 ⟨9, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83772309992939 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366251760891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_10 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (3349491998549 / 4000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183127867909 / 50000000000000 : ℝ))
      (E := (cell11922 ⟨10, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (3349491998549 / 4000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183127867909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_11 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (5231394681937 / 6250000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366259717297 / 100000000000000 : ℝ))
      (E := (cell11922 ⟨11, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (5231394681937 / 6250000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366259717297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_12 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83667354799151 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (236626365533 / 10000000000000 : ℝ))
      (E := (cell11922 ⟨12, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83667354799151 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (236626365533 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_13 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83632419592801 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (59156691841 / 2500000000000 : ℝ))
      (E := (cell11922 ⟨13, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83632419592801 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (59156691841 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_14 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83597509256727 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (23662716637 / 1000000000000 : ℝ))
      (E := (cell11922 ⟨14, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83597509256727 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (23662716637 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_15 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (41781311877949 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183137816341 / 50000000000000 : ℝ))
      (E := (cell11922 ⟨15, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (41781311877949 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183137816341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_16 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83527763055463 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183139793757 / 50000000000000 : ℝ))
      (E := (cell11922 ⟨16, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83527763055463 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183139793757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_17 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (41746463560379 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366283592987 / 100000000000000 : ℝ))
      (E := (cell11922 ⟨17, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (41746463560379 / 50000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366283592987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_18 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83458115917297 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366287539317 / 100000000000000 : ℝ))
      (E := (cell11922 ⟨18, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83458115917297 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (2366287539317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11922_19 : CellCertificate 11922 (909787845619949 / 10000000000000000 : ℝ) (220232337039767 / 125000000000000000 : ℝ) (356871933138809 / 10000000000000000 : ℝ)
    (cell11922 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · norm_num [cell11922]
  · have h := gap_lower (n := 11922) (a := (83423329410773 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183145774473 / 50000000000000 : ℝ))
      (E := (cell11922 ⟨19, by decide⟩).energy) (xi := (356871933138809 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11922 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11922) (a := (83423329410773 / 100000000000000 : ℝ)) (b := (173014155777 / 100000000000000 : ℝ)) (q := (1183145774473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11922]

theorem cert11923_0 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (8408851299381 / 10000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366020683607 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨0, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (8408851299381 / 10000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366020683607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_1 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (8405327689629 / 10000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183012307417 / 50000000000000 : ℝ))
      (E := (cell11923 ⟨1, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (8405327689629 / 10000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183012307417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_2 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (1680361322073 / 2000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366028642851 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨2, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (1680361322073 / 2000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366028642851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_3 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (16796576115713 / 20000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366032604837 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨3, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (16796576115713 / 20000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366032604837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_4 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (83947720283909 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366036568673 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨4, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (83947720283909 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366036568673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_5 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (41956292591377 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366040544233 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨5, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (41956292591377 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366040544233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_6 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (41938737619183 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366044541133 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨6, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (41938737619183 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366044541133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_7 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (41921195207103 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (591512127711 / 25000000000000 : ℝ))
      (E := (cell11923 ⟨7, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (41921195207103 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (591512127711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_8 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (83807330673927 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (295756565037 / 12500000000000 : ℝ))
      (E := (cell11923 ⟨8, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (83807330673927 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (295756565037 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_9 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (670178367851 / 800000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366056462467 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨9, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (670178367851 / 800000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366056462467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_10 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (41868643150293 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366060461703 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨10, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (41868643150293 / 50000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366060461703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_11 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (16740460319157 / 20000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (18484878659 / 781250000000 : ℝ))
      (E := (cell11923 ⟨11, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (16740460319157 / 20000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (18484878659 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_12 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (10458417728923 / 12500000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366068432413 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨12, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (10458417728923 / 12500000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366068432413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_13 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (5227025435749 / 6250000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183036209793 / 50000000000000 : ℝ))
      (E := (cell11923 ⟨13, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (5227025435749 / 6250000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183036209793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_14 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (8359749698237 / 10000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183038189659 / 50000000000000 : ℝ))
      (E := (cell11923 ⟨14, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (8359749698237 / 10000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183038189659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_15 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (83562611827511 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183040188427 / 50000000000000 : ℝ))
      (E := (cell11923 ⟨15, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (83562611827511 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (1183040188427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_16 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (1044096893407 / 1250000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366084361093 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨16, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (1044096893407 / 1250000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366084361093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_17 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (20873228970713 / 25000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366088338709 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨17, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (20873228970713 / 25000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366088338709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_18 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (83458105023901 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (591523079033 / 25000000000000 : ℝ))
      (E := (cell11923 ⟨18, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (83458105023901 / 100000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (591523079033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11923_19 : CellCertificate 11923 (909756293493243 / 10000000000000000 : ℝ) (1761710874820107 / 1000000000000000000 : ℝ) (44605150524977 / 1250000000000000 : ℝ)
    (cell11923 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · norm_num [cell11923]
  · have h := gap_lower (n := 11923) (a := (20855829715351 / 25000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366096299539 / 100000000000000 : ℝ))
      (E := (cell11923 ⟨19, by decide⟩).energy) (xi := (44605150524977 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11923 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11923) (a := (20855829715351 / 25000000000000 : ℝ)) (b := (17299945149 / 10000000000000 : ℝ)) (q := (2366096299539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11923]

theorem cert11924_0 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (21022123956737 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182912830499 / 50000000000000 : ℝ))
      (E := (cell11924 ⟨0, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (21022123956737 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182912830499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_1 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (21013315020573 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (118291480449 / 5000000000000 : ℝ))
      (E := (cell11924 ⟨1, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (21013315020573 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (118291480449 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_2 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (84018049642013 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182916798429 / 50000000000000 : ℝ))
      (E := (cell11924 ⟨2, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (84018049642013 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182916798429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_3 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (83982864468787 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (473167515463 / 20000000000000 : ℝ))
      (E := (cell11924 ⟨3, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (83982864468787 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (473167515463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_4 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (83947704525491 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (295730195061 / 12500000000000 : ℝ))
      (E := (cell11924 ⟨4, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (83947704525491 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (295730195061 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_5 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (20978142443799 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365845556253 / 100000000000000 : ℝ))
      (E := (cell11924 ⟨5, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (20978142443799 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365845556253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_6 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (8387746018117 / 10000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365849516363 / 100000000000000 : ℝ))
      (E := (cell11924 ⟨6, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (8387746018117 / 10000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365849516363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_7 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (41921187853437 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (473170701597 / 20000000000000 : ℝ))
      (E := (cell11924 ⟨7, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (41921187853437 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (473170701597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_8 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (20951829078991 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (473171496461 / 20000000000000 : ℝ))
      (E := (cell11924 ⟨8, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (20951829078991 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (473171496461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_9 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (41886140986143 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182930753009 / 50000000000000 : ℝ))
      (E := (cell11924 ⟨9, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (41886140986143 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182930753009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_10 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (20934318159969 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182932735899 / 50000000000000 : ℝ))
      (E := (cell11924 ⟨10, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (20934318159969 / 25000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182932735899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_11 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (41851144141481 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365869445803 / 100000000000000 : ℝ))
      (E := (cell11924 ⟨11, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (41851144141481 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365869445803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_12 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (83667328865957 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365873436033 / 100000000000000 : ℝ))
      (E := (cell11924 ⟨12, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (83667328865957 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365873436033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_13 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (83632394353461 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (236587739221 / 10000000000000 : ℝ))
      (E := (cell11924 ⟨13, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (83632394353461 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (236587739221 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_14 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (41798742355131 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182940689901 / 50000000000000 : ℝ))
      (E := (cell11924 ⟨14, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (41798742355131 / 50000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182940689901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_15 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (83562599901329 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (147867834249 / 6250000000000 : ℝ))
      (E := (cell11924 ⟨15, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (83562599901329 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (147867834249 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_16 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (83527739891817 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365889361771 / 100000000000000 : ℝ))
      (E := (cell11924 ⟨16, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (83527739891817 / 100000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365889361771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_17 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (4174645232353 / 5000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365893311673 / 100000000000000 : ℝ))
      (E := (cell11924 ⟨17, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (4174645232353 / 5000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (2365893311673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_18 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (2608065441643 / 3125000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182948660163 / 50000000000000 : ℝ))
      (E := (cell11924 ⟨18, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (2608065441643 / 3125000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182948660163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11924_19 : CellCertificate 11924 (181944949296031 / 2000000000000000 : ℝ) (880781539062351 / 500000000000000000 : ℝ) (356810480761621 / 10000000000000000 : ℝ)
    (cell11924 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · norm_num [cell11924]
  · have h := gap_lower (n := 11924) (a := (4171165415703 / 5000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182950638827 / 50000000000000 : ℝ))
      (E := (cell11924 ⟨19, by decide⟩).energy) (xi := (356810480761621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11924 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11924) (a := (4171165415703 / 5000000000000 : ℝ)) (b := (21623093719 / 12500000000000 : ℝ)) (q := (1182950638827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11924]

theorem cert11925_0 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (8408847866297 / 10000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (473126172647 / 20000000000000 : ℝ))
      (E := (cell11925 ⟨0, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (8408847866297 / 10000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (473126172647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_1 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (84053243271131 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182817442929 / 50000000000000 : ℝ))
      (E := (cell11925 ⟨1, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (84053243271131 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182817442929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_2 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (84018033183167 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365638833761 / 100000000000000 : ℝ))
      (E := (cell11925 ⟨2, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (84018033183167 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365638833761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_3 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (20995712090439 / 25000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365642832853 / 100000000000000 : ℝ))
      (E := (cell11925 ⟨3, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (20995712090439 / 25000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365642832853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_4 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (83947688769773 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365646835529 / 100000000000000 : ℝ))
      (E := (cell11925 ⟨4, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (83947688769773 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365646835529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_5 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (20978138592573 / 25000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (591412698457 / 25000000000000 : ℝ))
      (E := (cell11925 ⟨5, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (20978138592573 / 25000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (591412698457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_6 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (41938722563291 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365654775149 / 100000000000000 : ℝ))
      (E := (cell11925 ⟨6, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (41938722563291 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365654775149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_7 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (41921180501053 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182829365481 / 50000000000000 : ℝ))
      (E := (cell11925 ⟨7, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (41921180501053 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182829365481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_8 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (83807301960519 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (591415682049 / 25000000000000 : ℝ))
      (E := (cell11925 ⟨8, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (83807301960519 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (591415682049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_9 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (8377226796567 / 10000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (591416679439 / 25000000000000 : ℝ))
      (E := (cell11925 ⟨9, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (8377226796567 / 10000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (591416679439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_10 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (16747451796319 / 20000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (47313414163 / 2000000000000 : ℝ))
      (E := (cell11925 ⟨10, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (16747451796319 / 20000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (47313414163 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_11 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (83702274972523 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (236567470763 / 10000000000000 : ℝ))
      (E := (cell11925 ⟨11, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (83702274972523 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (236567470763 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_12 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (20916828975717 / 25000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (147854916637 / 6250000000000 : ℝ))
      (E := (cell11925 ⟨12, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (20916828975717 / 25000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (147854916637 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_13 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (5227023858577 / 6250000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (36963791399 / 1562500000000 : ℝ))
      (E := (cell11925 ⟨13, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (5227023858577 / 6250000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (36963791399 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_14 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (41798736220201 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365686607107 / 100000000000000 : ℝ))
      (E := (cell11925 ⟨14, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (41798736220201 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365686607107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_15 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (83562587977351 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182845302073 / 50000000000000 : ℝ))
      (E := (cell11925 ⟨15, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (83562587977351 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182845302073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_16 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (5220483019577 / 6250000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365694589551 / 100000000000000 : ℝ))
      (E := (cell11925 ⟨16, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (5220483019577 / 6250000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365694589551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_17 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (83492893413383 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182849284997 / 50000000000000 : ℝ))
      (E := (cell11925 ⟨17, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (83492893413383 / 100000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182849284997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_18 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (2086452081083 / 2500000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365702551903 / 100000000000000 : ℝ))
      (E := (cell11925 ⟨18, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (2086452081083 / 2500000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (2365702551903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11925_19 : CellCertificate 11925 (113711650572423 / 1250000000000000 : ℝ) (1761415306225681 / 1000000000000000000 : ℝ) (178389881411237 / 5000000000000000 : ℝ)
    (cell11925 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · norm_num [cell11925]
  · have h := gap_lower (n := 11925) (a := (41711648884371 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182853270727 / 50000000000000 : ℝ))
      (E := (cell11925 ⟨19, by decide⟩).energy) (xi := (178389881411237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11925 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11925) (a := (41711648884371 / 50000000000000 : ℝ)) (b := (43242512641 / 25000000000000 : ℝ)) (q := (1182853270727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11925]

theorem cert11926_0 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (84088461501873 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473087269609 / 20000000000000 : ℝ))
      (E := (cell11926 ⟨0, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (84088461501873 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473087269609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_1 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (84053226462807 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365440329987 / 100000000000000 : ℝ))
      (E := (cell11926 ⟨1, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (84053226462807 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365440329987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_2 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (84018016727113 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365444353563 / 100000000000000 : ℝ))
      (E := (cell11926 ⟨2, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (84018016727113 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365444353563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_3 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (8398283225747 / 10000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (1182724156833 / 50000000000000 : ℝ))
      (E := (cell11926 ⟨3, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (8398283225747 / 10000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (1182724156833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_4 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (16789534603351 / 20000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (1182726139087 / 50000000000000 : ℝ))
      (E := (cell11926 ⟨4, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (16789534603351 / 20000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (1182726139087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_5 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (83912538968043 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365456256959 / 100000000000000 : ℝ))
      (E := (cell11926 ⟨5, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (83912538968043 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365456256959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_6 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (20969357518651 / 25000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (147841266227 / 6250000000000 : ℝ))
      (E := (cell11926 ⟨6, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (20969357518651 / 25000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (147841266227 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_7 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (41921173149951 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365464237661 / 100000000000000 : ℝ))
      (E := (cell11926 ⟨7, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (41921173149951 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365464237661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_8 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (83807287607593 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (591367050017 / 25000000000000 : ℝ))
      (E := (cell11926 ⟨8, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (83807287607593 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (591367050017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_9 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (83772253961527 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (1182736106773 / 50000000000000 : ℝ))
      (E := (cell11926 ⟨9, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (83772253961527 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (1182736106773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_10 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (41868622662871 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473095234153 / 20000000000000 : ℝ))
      (E := (cell11926 ⟨10, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (41868622662871 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473095234153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_11 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (41851130832233 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365480137883 / 100000000000000 : ℝ))
      (E := (cell11926 ⟨11, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (41851130832233 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365480137883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_12 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (20916825735529 / 25000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (147842757681 / 6250000000000 : ℝ))
      (E := (cell11926 ⟨12, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (20916825735529 / 25000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (147842757681 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_13 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (16726473824659 / 20000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (591372033387 / 25000000000000 : ℝ))
      (E := (cell11926 ⟨13, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (16726473824659 / 20000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (591372033387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_14 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (83597460172791 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365492119283 / 100000000000000 : ℝ))
      (E := (cell11926 ⟨14, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (83597460172791 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365492119283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_15 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (10445322006947 / 12500000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (295687010909 / 12500000000000 : ℝ))
      (E := (cell11926 ⟨15, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (10445322006947 / 12500000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (295687010909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_16 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (41763858368403 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473100008887 / 20000000000000 : ℝ))
      (E := (cell11926 ⟨16, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (41763858368403 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473100008887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_17 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (83492882181819 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365504055563 / 100000000000000 : ℝ))
      (E := (cell11926 ⟨17, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (83492882181819 / 100000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (2365504055563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_18 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (41729036178067 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473101602173 / 20000000000000 : ℝ))
      (E := (cell11926 ⟨18, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (41729036178067 / 50000000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (473101602173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11926_19 : CellCertificate 11926 (909661667789629 / 10000000000000000 : ℝ) (880633779558401 / 500000000000000000 : ℝ) (178374525190313 / 5000000000000000 : ℝ)
    (cell11926 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · norm_num [cell11926]
  · have h := gap_lower (n := 11926) (a := (10427910903181 / 12500000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (118275601639 / 5000000000000 : ℝ))
      (E := (cell11926 ⟨19, by decide⟩).energy) (xi := (178374525190313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11926 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11926) (a := (10427910903181 / 12500000000000 : ℝ)) (b := (43238838481 / 25000000000000 : ℝ)) (q := (118275601639 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11926]

theorem cert11927_0 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (84088444343659 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365242057707 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨0, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (84088444343659 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365242057707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_1 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (84053209657319 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365246056853 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨1, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (84053209657319 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365246056853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_2 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (84018000273849 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365250040737 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨2, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (84018000273849 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365250040737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_3 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (10497852019491 / 12500000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365254019759 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨3, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (10497852019491 / 12500000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365254019759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_4 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (20986914316609 / 25000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365258004051 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨4, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (20986914316609 / 25000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365258004051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_5 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (1311133180757 / 1562500000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365262003487 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨5, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (1311133180757 / 1562500000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365262003487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_6 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (41938707512617 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365265969817 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨6, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (41938707512617 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365265969817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_7 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (4192116580013 / 5000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (591317492551 / 25000000000000 : ℝ))
      (E := (cell11927 ⟨7, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (4192116580013 / 5000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (591317492551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_8 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (2618977289287 / 3125000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (591318474481 / 25000000000000 : ℝ))
      (E := (cell11927 ⟨8, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (2618977289287 / 3125000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (591318474481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_9 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (5235764997491 / 6250000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (118263896773 / 5000000000000 : ℝ))
      (E := (cell11927 ⟨9, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (5235764997491 / 6250000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (118263896773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_10 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (16747446334463 / 20000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (1182640958799 / 50000000000000 : ℝ))
      (E := (cell11927 ⟨10, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (16747446334463 / 20000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (1182640958799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_11 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (10462781044849 / 12500000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365285852517 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨11, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (10462781044849 / 12500000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365285852517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_12 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (41833644991851 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (473057972829 / 20000000000000 : ℝ))
      (E := (cell11927 ⟨12, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (41833644991851 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (473057972829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_13 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (83632356511651 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (473058768849 / 20000000000000 : ℝ))
      (E := (cell11927 ⟨13, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (83632356511651 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (473058768849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_14 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (41798723953713 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (29566222503 / 1250000000000 : ℝ))
      (E := (cell11927 ⟨14, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (41798723953713 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (29566222503 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_15 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (83562564136003 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365301797367 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨15, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (83562564136003 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365301797367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_16 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (41763852581269 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (1182652892261 / 50000000000000 : ℝ))
      (E := (cell11927 ⟨16, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (41763852581269 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (1182652892261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_17 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (83492870952369 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (1182654884189 / 50000000000000 : ℝ))
      (E := (cell11927 ⟨17, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (83492870952369 / 100000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (1182654884189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_18 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (10432257683877 / 12500000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365313755357 / 100000000000000 : ℝ))
      (E := (cell11927 ⟨18, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (10432257683877 / 12500000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (2365313755357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11927_19 : CellCertificate 11927 (90963013610959 / 1000000000000000 : ℝ) (440279959197957 / 250000000000000000 : ℝ) (44589792929291 / 1250000000000000 : ℝ)
    (cell11927 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · norm_num [cell11927]
  · have h := gap_lower (n := 11927) (a := (41711638342089 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (591329437909 / 25000000000000 : ℝ))
      (E := (cell11927 ⟨19, by decide⟩).energy) (xi := (44589792929291 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11927 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11927) (a := (41711638342089 / 50000000000000 : ℝ)) (b := (21617582479 / 12500000000000 : ℝ)) (q := (591329437909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11927]

theorem cert11928_0 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (3363537087533 / 4000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365048049947 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨0, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (3363537087533 / 4000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365048049947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_1 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (42026596427333 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365052008719 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨1, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (42026596427333 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365052008719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_2 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (42008991911687 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365056010817 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨2, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (42008991911687 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365056010817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_3 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (8398280005713 / 10000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (591264987783 / 25000000000000 : ℝ))
      (E := (cell11928 ⟨3, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (8398280005713 / 10000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (591264987783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_4 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (16789528303763 / 20000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365063955351 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨4, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (16789528303763 / 20000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365063955351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_5 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (16782501634301 / 20000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (1182533958871 / 50000000000000 : ℝ))
      (E := (cell11928 ⟨5, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (16782501634301 / 20000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (1182533958871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_6 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83877399978471 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365071905707 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨6, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83877399978471 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365071905707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_7 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83842316903181 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365075870707 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨7, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83842316903181 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365075870707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_8 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83807258909293 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365079879671 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨8, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83807258909293 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365079879671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_9 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83772225960657 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (4730167767 / 200000000000 : ℝ))
      (E := (cell11928 ⟨9, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83772225960657 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (4730167767 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_10 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (20934304505329 / 25000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (295635979093 / 12500000000000 : ℝ))
      (E := (cell11928 ⟨10, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (20934304505329 / 25000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (295635979093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_11 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83702235055499 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365091851537 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨11, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83702235055499 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365091851537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_12 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (10458409628453 / 12500000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (295636978993 / 12500000000000 : ℝ))
      (E := (cell11928 ⟨12, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (10458409628453 / 12500000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (295636978993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_13 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (41816171951149 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (4619335511 / 195312500000 : ℝ))
      (E := (cell11928 ⟨13, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (41816171951149 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (4619335511 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_14 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83597435644309 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (295637970759 / 12500000000000 : ℝ))
      (E := (cell11928 ⟨14, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83597435644309 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (295637970759 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_15 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83562552218633 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (236510773443 / 10000000000000 : ℝ))
      (E := (cell11928 ⟨15, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83562552218633 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (236510773443 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_16 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83527693590427 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (59127793793 / 2500000000000 : ℝ))
      (E := (cell11928 ⟨16, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83527693590427 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (59127793793 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_17 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (83492859725031 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (591278927111 / 25000000000000 : ℝ))
      (E := (cell11928 ⟨17, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (83492859725031 / 100000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (591278927111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_18 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (41729025293983 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365119669097 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨18, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (41729025293983 / 50000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365119669097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11928_19 : CellCertificate 11928 (909598609537967 / 10000000000000000 : ℝ) (440243034811131 / 250000000000000000 : ℝ) (44585955247729 / 1250000000000000 : ℝ)
    (cell11928 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · norm_num [cell11928]
  · have h := gap_lower (n := 11928) (a := (20855816536233 / 25000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365123698021 / 100000000000000 : ℝ))
      (E := (cell11928 ⟨19, by decide⟩).energy) (xi := (44585955247729 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11928 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11928) (a := (20855816536233 / 25000000000000 : ℝ)) (b := (5403936509 / 3125000000000 : ℝ)) (q := (2365123698021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11928]

theorem cert11929_0 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (84088410035871 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (236485420933 / 10000000000000 : ℝ))
      (E := (cell11929 ⟨0, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (84088410035871 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (236485420933 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_1 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (84053176054847 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591214546397 / 25000000000000 : ℝ))
      (E := (cell11929 ⟨1, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (84053176054847 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591214546397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_2 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (10502245921961 / 12500000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364862206041 / 100000000000000 : ℝ))
      (E := (cell11929 ⟨2, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (10502245921961 / 12500000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364862206041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_3 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (20995695990269 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364866165579 / 100000000000000 : ℝ))
      (E := (cell11929 ⟨3, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (20995695990269 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364866165579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_4 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (20986906443473 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591217533019 / 25000000000000 : ℝ))
      (E := (cell11929 ⟨4, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (20986906443473 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591217533019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_5 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (41956246388607 / 50000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (1182437057701 / 50000000000000 : ℝ))
      (E := (cell11929 ⟨5, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (41956246388607 / 50000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (1182437057701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_6 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (20969346233579 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364878125163 / 100000000000000 : ℝ))
      (E := (cell11929 ⟨6, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (20969346233579 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364878125163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_7 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (83842302208663 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364882112827 / 100000000000000 : ℝ))
      (E := (cell11929 ⟨7, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (83842302208663 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364882112827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_8 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (83807244563917 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364886087409 / 100000000000000 : ℝ))
      (E := (cell11929 ⟨8, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (83807244563917 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364886087409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_9 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (83772211963929 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (295611257209 / 12500000000000 : ℝ))
      (E := (cell11929 ⟨9, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (83772211963929 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (295611257209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_10 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (41868602186371 / 50000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591223508029 / 25000000000000 : ℝ))
      (E := (cell11929 ⟨10, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (41868602186371 / 50000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591223508029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_11 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (83702221754587 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364898018993 / 100000000000000 : ℝ))
      (E := (cell11929 ⟨11, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (83702221754587 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364898018993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_12 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (41833632036941 / 50000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (1182450984147 / 50000000000000 : ℝ))
      (E := (cell11929 ⟨12, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (41833632036941 / 50000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (1182450984147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_13 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (20908082823809 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364906003737 / 100000000000000 : ℝ))
      (E := (cell11929 ⟨13, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (20908082823809 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (2364906003737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_14 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (83597423383437 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (118245497937 / 5000000000000 : ℝ))
      (E := (cell11929 ⟨14, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (83597423383437 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (118245497937 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_15 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (83562540303463 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (118245697827 / 5000000000000 : ℝ))
      (E := (cell11929 ⟨15, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (83562540303463 / 100000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (118245697827 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_16 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (10440960252559 / 12500000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (147807371627 / 6250000000000 : ℝ))
      (E := (cell11929 ⟨16, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (10440960252559 / 12500000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (147807371627 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_17 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (16698569699961 / 20000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591230483471 / 25000000000000 : ℝ))
      (E := (cell11929 ⟨17, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (16698569699961 / 20000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (591230483471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_18 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (10432254963373 / 12500000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (18919406947 / 800000000000 : ℝ))
      (E := (cell11929 ⟨18, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (10432254963373 / 12500000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (18919406947 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11929_19 : CellCertificate 11929 (909567088073461 / 10000000000000000 : ℝ) (1760824466468657 / 1000000000000000000 : ℝ) (178328473010697 / 5000000000000000 : ℝ)
    (cell11929 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · norm_num [cell11929]
  · have h := gap_lower (n := 11929) (a := (20855813901927 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (1182464935971 / 50000000000000 : ℝ))
      (E := (cell11929 ⟨19, by decide⟩).energy) (xi := (178328473010697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11929 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11929) (a := (20855813901927 / 25000000000000 : ℝ)) (b := (17291127929 / 10000000000000 : ℝ)) (q := (1182464935971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11929]

theorem cert11930_0 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (84088392886297 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (73895645353 / 3125000000000 : ℝ))
      (E := (cell11930 ⟨0, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (84088392886297 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (73895645353 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_1 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (42026579628931 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (472932929041 / 20000000000000 : ℝ))
      (E := (cell11930 ⟨1, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (42026579628931 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (472932929041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_2 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (8401795093079 / 10000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (591167156603 / 25000000000000 : ℝ))
      (E := (cell11930 ⟨2, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (8401795093079 / 10000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (591167156603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_3 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (20995691966941 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (472934521063 / 20000000000000 : ℝ))
      (E := (cell11930 ⟨3, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (20995691966941 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (472934521063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_4 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (41973805015833 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (591169148011 / 25000000000000 : ℝ))
      (E := (cell11930 ⟨4, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (41973805015833 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (591169148011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_5 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (3356499095423 / 4000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364680538631 / 100000000000000 : ℝ))
      (E := (cell11930 ⟨5, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (3356499095423 / 4000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364680538631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_6 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (41938684946383 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (295585564059 / 12500000000000 : ℝ))
      (E := (cell11930 ⟨6, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (41938684946383 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (295585564059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_7 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (41921143758353 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (472937704583 / 20000000000000 : ℝ))
      (E := (cell11930 ⟨7, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (41921143758353 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (472937704583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_8 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (83807230221057 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (118234626057 / 5000000000000 : ℝ))
      (E := (cell11930 ⟨8, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (83807230221057 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (118234626057 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_9 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (10471524746209 / 12500000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (295587057247 / 12500000000000 : ℝ))
      (E := (cell11930 ⟨9, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (10471524746209 / 12500000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (295587057247 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_10 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (83737190726593 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364700457763 / 100000000000000 : ℝ))
      (E := (cell11930 ⟨10, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (83737190726593 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364700457763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_11 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (16740441691211 / 20000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (59117611771 / 2500000000000 : ℝ))
      (E := (cell11930 ⟨11, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (16740441691211 / 20000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (59117611771 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_12 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (20916812780619 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364708447201 / 100000000000000 : ℝ))
      (E := (cell11930 ⟨12, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (20916812780619 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364708447201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_13 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (2613509959077 / 3125000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364712394513 / 100000000000000 : ℝ))
      (E := (cell11930 ⟨13, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (2613509959077 / 3125000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364712394513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_14 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (83597411124811 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364716378243 / 100000000000000 : ℝ))
      (E := (cell11930 ⟨14, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (83597411124811 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364716378243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_15 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (16712505678099 / 20000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (1182360173777 / 50000000000000 : ℝ))
      (E := (cell11930 ⟨15, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (16712505678099 / 20000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (1182360173777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_16 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (41763835226337 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364724367461 / 100000000000000 : ℝ))
      (E := (cell11930 ⟨16, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (41763835226337 / 50000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (2364724367461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_17 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (83492837276691 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (1182364164231 / 50000000000000 : ℝ))
      (E := (cell11930 ⟨17, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (83492837276691 / 100000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (1182364164231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_18 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (20864507207017 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (47294645901 / 2000000000000 : ℝ))
      (E := (cell11930 ⟨18, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (20864507207017 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (47294645901 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11930_19 : CellCertificate 11930 (909535571714773 / 10000000000000000 : ℝ) (880338409228997 / 500000000000000000 : ℝ) (178313127775633 / 5000000000000000 : ℝ)
    (cell11930 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · norm_num [cell11930]
  · have h := gap_lower (n := 11930) (a := (20855811268127 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (11823681367 / 500000000000 : ℝ))
      (E := (cell11930 ⟨19, by decide⟩).energy) (xi := (178313127775633 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11930 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11930) (a := (20855811268127 / 25000000000000 : ℝ)) (b := (86448296419 / 50000000000000 : ℝ)) (q := (11823681367 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11930]

theorem cert11931_0 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (42044187869801 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (236446731813 / 10000000000000 : ℝ))
      (E := (cell11931 ⟨0, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (42044187869801 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (236446731813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_1 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (8405314246371 / 10000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (295558909011 / 12500000000000 : ℝ))
      (E := (cell11931 ⟨1, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (8405314246371 / 10000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (295558909011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_2 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (84017934488679 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182237635967 / 50000000000000 : ℝ))
      (E := (cell11931 ⟨2, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (84017934488679 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182237635967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_3 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (41991375888597 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364479270343 / 100000000000000 : ℝ))
      (E := (cell11931 ⟨3, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (41991375888597 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364479270343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_4 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (10493449286517 / 12500000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (147780201227 / 6250000000000 : ℝ))
      (E := (cell11931 ⟨4, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (10493449286517 / 12500000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (147780201227 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_5 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (83912461996587 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182243593717 / 50000000000000 : ℝ))
      (E := (cell11931 ⟨5, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (83912461996587 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182243593717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_6 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (41938677426911 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (472898236671 / 20000000000000 : ℝ))
      (E := (cell11931 ⟨6, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (41938677426911 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (472898236671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_7 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (83842272827309 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364495158859 / 100000000000000 : ℝ))
      (E := (cell11931 ⟨7, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (83842272827309 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364495158859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_8 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (10475901985089 / 12500000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (591124795217 / 25000000000000 : ℝ))
      (E := (cell11931 ⟨8, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (10475901985089 / 12500000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (591124795217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_9 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (20943045994471 / 25000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (591125785587 / 25000000000000 : ℝ))
      (E := (cell11931 ⟨9, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (20943045994471 / 25000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (591125785587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_10 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (8373717708287 / 10000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182253554843 / 50000000000000 : ℝ))
      (E := (cell11931 ⟨10, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (8373717708287 / 10000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182253554843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_11 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (83702195159903 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (295563886391 / 12500000000000 : ℝ))
      (E := (cell11931 ⟨11, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (83702195159903 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (295563886391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_12 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (20916809543351 / 25000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182257547333 / 50000000000000 : ℝ))
      (E := (cell11931 ⟨12, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (20916809543351 / 25000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182257547333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_13 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (41816153043991 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364519070013 / 100000000000000 : ℝ))
      (E := (cell11931 ⟨13, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (41816153043991 / 50000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364519070013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_14 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (8359739886843 / 10000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182261512293 / 50000000000000 : ℝ))
      (E := (cell11931 ⟨14, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (8359739886843 / 10000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (1182261512293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_15 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (83562516479727 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (118226351181 / 5000000000000 : ℝ))
      (E := (cell11931 ⟨15, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (83562516479727 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (118226351181 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_16 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (83527658887031 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (236453101601 / 10000000000000 : ℝ))
      (E := (cell11931 ⟨16, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (83527658887031 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (236453101601 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_17 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (10436603256961 / 12500000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364535008419 / 100000000000000 : ℝ))
      (E := (cell11931 ⟨17, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (10436603256961 / 12500000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364535008419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_18 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (83458017951219 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364539007269 / 100000000000000 : ℝ))
      (E := (cell11931 ⟨18, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (83458017951219 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (2364539007269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11931_19 : CellCertificate 11931 (181900812092121 / 2000000000000000 : ℝ) (1760529195206307 / 1000000000000000000 : ℝ) (356595570569707 / 10000000000000000 : ℝ)
    (cell11931 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · norm_num [cell11931]
  · have h := gap_lower (n := 11931) (a := (83423234539329 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (591135740141 / 25000000000000 : ℝ))
      (E := (cell11931 ⟨19, by decide⟩).energy) (xi := (356595570569707 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11931 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11931) (a := (83423234539329 / 100000000000000 : ℝ)) (b := (172881908931 / 100000000000000 : ℝ)) (q := (591135740141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11931]

theorem cert11932_0 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (10511044824473 / 12500000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (591068552459 / 25000000000000 : ℝ))
      (E := (cell11932 ⟨0, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (10511044824473 / 12500000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (591068552459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_1 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (84053125672391 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364278181727 / 100000000000000 : ℝ))
      (E := (cell11932 ⟨1, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (84053125672391 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364278181727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_2 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (16803583609871 / 20000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (236428214261 / 10000000000000 : ℝ))
      (E := (cell11932 ⟨2, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (16803583609871 / 20000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (236428214261 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_3 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (20995683922341 / 25000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182143080333 / 50000000000000 : ℝ))
      (E := (cell11932 ⟨3, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (20995683922341 / 25000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182143080333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_4 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (41973789277651 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364290130469 / 100000000000000 : ℝ))
      (E := (cell11932 ⟨4, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (41973789277651 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364290130469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_5 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (83912446610249 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364294119651 / 100000000000000 : ℝ))
      (E := (cell11932 ⟨5, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (83912446610249 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364294119651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_6 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (41938669908741 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364298079957 / 100000000000000 : ℝ))
      (E := (cell11932 ⟨6, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (41938669908741 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364298079957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_7 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (10480282267559 / 12500000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (472860415709 / 20000000000000 : ℝ))
      (E := (cell11932 ⟨7, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (10480282267559 / 12500000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (472860415709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_8 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (83807201542881 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (472861213319 / 20000000000000 : ℝ))
      (E := (cell11932 ⟨8, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (83807201542881 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (472861213319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_9 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (16754433997713 / 20000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182155026431 / 50000000000000 : ℝ))
      (E := (cell11932 ⟨9, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (16754433997713 / 20000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182155026431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_10 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (8373716344157 / 10000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182157022923 / 50000000000000 : ℝ))
      (E := (cell11932 ⟨10, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (8373716344157 / 10000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182157022923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_11 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (83702181866129 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364317995817 / 100000000000000 : ℝ))
      (E := (cell11932 ⟨11, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (83702181866129 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364317995817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_12 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (41833612613333 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182160984347 / 50000000000000 : ℝ))
      (E := (cell11932 ⟨12, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (41833612613333 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182160984347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_13 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (8363229348779 / 10000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (295540746527 / 12500000000000 : ℝ))
      (E := (cell11932 ⟨13, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (8363229348779 / 10000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (295540746527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_14 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (41798693307147 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (118216497791 / 5000000000000 : ℝ))
      (E := (cell11932 ⟨14, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (41798693307147 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (118216497791 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_15 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (41781252285579 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364333926671 / 100000000000000 : ℝ))
      (E := (cell11932 ⟨15, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (41781252285579 / 50000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (2364333926671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_16 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (10440955915443 / 12500000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182168945841 / 50000000000000 : ℝ))
      (E := (cell11932 ⟨16, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (10440955915443 / 12500000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182168945841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_17 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (16698562967359 / 20000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (59108547891 / 2500000000000 : ℝ))
      (E := (cell11932 ⟨17, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (16698562967359 / 20000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (59108547891 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_18 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (20864501769109 / 25000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (591086472187 / 25000000000000 : ℝ))
      (E := (cell11932 ⟨18, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (20864501769109 / 25000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (591086472187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11932_19 : CellCertificate 11932 (454736277154829 / 5000000000000000 : ℝ) (220047699588421 / 125000000000000000 : ℝ) (89141222768743 / 2500000000000000 : ℝ)
    (cell11932 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · norm_num [cell11932]
  · have h := gap_lower (n := 11932) (a := (83423224008171 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182174937637 / 50000000000000 : ℝ))
      (E := (cell11932 ⟨19, by decide⟩).energy) (xi := (89141222768743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11932 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11932) (a := (83423224008171 / 100000000000000 : ℝ)) (b := (10804201723 / 6250000000000 : ℝ)) (q := (1182174937637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11932]

theorem cert11933_0 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (21022085363711 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (147755082901 / 6250000000000 : ℝ))
      (E := (cell11933 ⟨0, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (21022085363711 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (147755082901 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_1 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (84053108883903 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182042658191 / 50000000000000 : ℝ))
      (E := (cell11933 ⟨1, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (84053108883903 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182042658191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_2 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (84017901612817 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364089296209 / 100000000000000 : ℝ))
      (E := (cell11933 ⟨2, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (84017901612817 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364089296209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_3 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (20995679901069 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182046638143 / 50000000000000 : ℝ))
      (E := (cell11933 ⟨3, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (20995679901069 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182046638143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_4 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (83947562821163 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (295512158343 / 12500000000000 : ℝ))
      (E := (cell11933 ⟨4, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (83947562821163 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (295512158343 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_5 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (83912431226561 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (236410121961 / 10000000000000 : ℝ))
      (E := (cell11933 ⟨5, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (83912431226561 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (236410121961 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_6 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (83877324783747 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364105202279 / 100000000000000 : ℝ))
      (E := (cell11933 ⟨6, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (83877324783747 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364105202279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_7 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (83842243456193 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182054612047 / 50000000000000 : ℝ))
      (E := (cell11933 ⟨7, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (83842243456193 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182054612047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_8 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (20951796801891 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (591028294581 / 25000000000000 : ℝ))
      (E := (cell11933 ⟨8, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (20951796801891 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (591028294581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_9 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (16754431200343 / 20000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364117189517 / 100000000000000 : ℝ))
      (E := (cell11933 ⟨9, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (16754431200343 / 20000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364117189517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_10 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (41868574901347 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182060575167 / 50000000000000 : ℝ))
      (E := (cell11933 ⟨10, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (41868574901347 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182060575167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_11 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (16740433714947 / 20000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (147757820433 / 6250000000000 : ℝ))
      (E := (cell11933 ⟨11, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (16740433714947 / 20000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (147757820433 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_12 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (41833606141131 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364129127287 / 100000000000000 : ℝ))
      (E := (cell11933 ⟨12, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (41833606141131 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364129127287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_13 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (41816140444943 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364133101123 / 100000000000000 : ℝ))
      (E := (cell11933 ⟨13, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (41816140444943 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364133101123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_14 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (83597374362401 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (591034263963 / 25000000000000 : ℝ))
      (E := (cell11933 ⟨14, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (83597374362401 / 100000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (591034263963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_15 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (20890623166197 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364141056707 / 100000000000000 : ℝ))
      (E := (cell11933 ⟨15, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (20890623166197 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364141056707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_16 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (8352763576221 / 10000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364145052577 / 100000000000000 : ℝ))
      (E := (cell11933 ⟨16, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (8352763576221 / 10000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (2364145052577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_17 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (20873200905003 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (147759315633 / 6250000000000 : ℝ))
      (E := (cell11933 ⟨17, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (20873200905003 / 25000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (147759315633 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_18 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (41728998101859 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182076498817 / 50000000000000 : ℝ))
      (E := (cell11933 ⟨18, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (41728998101859 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (1182076498817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

theorem cert11933_19 : CellCertificate 11933 (227360263315159 / 2500000000000000 : ℝ) (220029252869369 / 125000000000000000 : ℝ) (356534217065319 / 10000000000000000 : ℝ)
    (cell11933 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · norm_num [cell11933]
  · have h := gap_lower (n := 11933) (a := (41711606739517 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (236415701753 / 10000000000000 : ℝ))
      (E := (cell11933 ⟨19, by decide⟩).energy) (xi := (356534217065319 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell11933 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell11933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell11933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 11933) (a := (41711606739517 / 50000000000000 : ℝ)) (b := (172852548749 / 100000000000000 : ℝ)) (q := (236415701753 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell11933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell11933]

end BstLean.Part281
