import BstLean.Part281CellData9

namespace BstLean.Part281
open Real BstLean.Part263

theorem cert12084_0 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (16817157154787 / 20000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337208793429 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨0, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (16817157154787 / 20000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337208793429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_1 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (42025302952253 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337212777083 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨1, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (42025302952253 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337212777083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_2 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (42007725629963 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (584304190529 / 25000000000000 : ℝ))
      (E := (cell12084 ⟨2, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (42007725629963 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (584304190529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_3 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (83980321803049 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337220758621 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨3, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (83980321803049 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337220758621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_4 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (41972608748463 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (9129784057 / 390625000000 : ℝ))
      (E := (cell12084 ⟨4, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (41972608748463 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (9129784057 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_5 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (20977534576201 / 25000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337228709383 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨5, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (20977534576201 / 25000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337228709383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_6 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (20968771047531 / 25000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337232682421 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨6, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (20968771047531 / 25000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337232682421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_7 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (83840055116519 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (584309176147 / 25000000000000 : ℝ))
      (E := (cell12084 ⟨7, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (83840055116519 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (584309176147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_8 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (10475631380977 / 12500000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (146077541801 / 6250000000000 : ℝ))
      (E := (cell12084 ⟨8, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (10475631380977 / 12500000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (146077541801 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_9 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (83770071948029 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (46744892829 / 2000000000000 : ℝ))
      (E := (cell12084 ⟨9, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (83770071948029 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (46744892829 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_10 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (41867558890683 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (292156078837 / 12500000000000 : ℝ))
      (E := (cell12084 ⟨10, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (41867558890683 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (292156078837 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_11 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (41850094256109 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (584313161127 / 25000000000000 : ℝ))
      (E := (cell12084 ⟨11, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (41850094256109 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (584313161127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_12 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (83665284105167 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337256632561 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨12, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (83665284105167 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337256632561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_13 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (41815202262489 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337260602231 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨13, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (41815202262489 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337260602231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_14 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (417977748683 / 500000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337264618717 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨14, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (417977748683 / 500000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337264618717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_15 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (5222544981573 / 6250000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (292158571597 / 12500000000000 : ℝ))
      (E := (cell12084 ⟨15, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (5222544981573 / 6250000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (292158571597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_16 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (83525914395997 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337272587199 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨16, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (83525914395997 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337272587199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_17 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (41745566887291 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (467455310431 / 20000000000000 : ℝ))
      (E := (cell12084 ⟨17, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (41745566887291 / 50000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (467455310431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_18 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (83456377806599 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337280531873 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨18, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (83456377806599 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337280531873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12084_19 : CellCertificate 12084 (180948439022593 / 2000000000000000 : ℝ) (1738230780482737 / 1000000000000000000 : ℝ) (351964391552871 / 10000000000000000 : ℝ)
    (cell12084 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · norm_num [cell12084]
  · have h := gap_lower (n := 12084) (a := (83421646457903 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337284532237 / 100000000000000 : ℝ))
      (E := (cell12084 ⟨19, by decide⟩).energy) (xi := (351964391552871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12084 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12084) (a := (83421646457903 / 100000000000000 : ℝ)) (b := (42666204863 / 25000000000000 : ℝ)) (q := (2337284532237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12084]

theorem cert12085_0 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (4204288453103 / 5000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337043313079 / 100000000000000 : ℝ))
      (E := (cell12085 ⟨0, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (4204288453103 / 5000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337043313079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_1 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (84050589538249 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (116852366669 / 5000000000000 : ℝ))
      (E := (cell12085 ⟨1, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (84050589538249 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (116852366669 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_2 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (21003858809699 / 25000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337051298131 / 100000000000000 : ℝ))
      (E := (cell12085 ⟨2, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (21003858809699 / 25000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337051298131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_3 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (16796061225311 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168527637583 / 50000000000000 : ℝ))
      (E := (cell12085 ⟨3, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (16796061225311 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168527637583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_4 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (4197260108229 / 5000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (233705927431 / 10000000000000 : ℝ))
      (E := (cell12085 ⟨4, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (4197260108229 / 5000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (233705927431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_5 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (83910123316117 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168531623637 / 50000000000000 : ℝ))
      (E := (cell12085 ⟨5, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (83910123316117 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168531623637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_6 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (2621095923269 / 3125000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (93482690447 / 4000000000000 : ℝ))
      (E := (cell12085 ⟨6, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (2621095923269 / 3125000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (93482690447 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_7 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (83840040813689 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337071267153 / 100000000000000 : ℝ))
      (E := (cell12085 ⟨7, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (83840040813689 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337071267153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_8 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (16761007417437 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (146067201 / 6250000000 : ℝ))
      (E := (cell12085 ⟨8, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (16761007417437 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (146067201 / 6250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_9 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (16754011665823 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337079232009 / 100000000000000 : ℝ))
      (E := (cell12085 ⟨9, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (16754011665823 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337079232009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_10 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (16747020900737 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (467416641501 / 20000000000000 : ℝ))
      (E := (cell12085 ⟨10, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (16747020900737 / 20000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (467416641501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_11 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (10462521946911 / 12500000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337087208371 / 100000000000000 : ℝ))
      (E := (cell12085 ⟨11, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (10462521946911 / 12500000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337087208371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_12 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (83665271508507 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337091184279 / 100000000000000 : ℝ))
      (E := (cell12085 ⟨12, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (83665271508507 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337091184279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_13 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (20907598067027 / 25000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (146068446413 / 6250000000000 : ℝ))
      (E := (cell12085 ⟨13, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (20907598067027 / 25000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (146068446413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_14 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (41797768909521 / 50000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (46741982971 / 2000000000000 : ℝ))
      (E := (cell12085 ⟨14, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (41797768909521 / 50000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (46741982971 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_15 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (20890177031611 / 25000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168551575479 / 50000000000000 : ℝ))
      (E := (cell12085 ⟨15, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (20890177031611 / 25000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168551575479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_16 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (83525903155629 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168553549171 / 50000000000000 : ℝ))
      (E := (cell12085 ⟨16, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (83525903155629 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (1168553549171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_17 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (41745561436047 / 50000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (584277778323 / 25000000000000 : ℝ))
      (E := (cell12085 ⟨17, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (41745561436047 / 50000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (584277778323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_18 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (83456367241517 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337115085681 / 100000000000000 : ℝ))
      (E := (cell12085 ⟨18, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (83456367241517 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (2337115085681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12085_19 : CellCertificate 12085 (226177863683037 / 2500000000000000 : ℝ) (347617379408553 / 200000000000000000 : ℝ) (351934531616593 / 10000000000000000 : ℝ)
    (cell12085 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · norm_num [cell12085]
  · have h := gap_lower (n := 12085) (a := (83421636229753 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (292139884939 / 12500000000000 : ℝ))
      (E := (cell12085 ⟨19, by decide⟩).energy) (xi := (351934531616593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12085 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12085) (a := (83421636229753 / 100000000000000 : ℝ)) (b := (170650519007 / 100000000000000 : ℝ)) (q := (292139884939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12085]

theorem cert12086_0 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (42042876176477 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (584219514511 / 25000000000000 : ℝ))
      (E := (cell12086 ⟨0, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (42042876176477 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (584219514511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_1 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (84050573174717 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336881999601 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨1, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (84050573174717 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336881999601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_2 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (84015419220347 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (46737720039 / 2000000000000 : ℝ))
      (E := (cell12086 ⟨2, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (84015419220347 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (46737720039 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_3 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83980290452699 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336890017441 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨3, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83980290452699 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336890017441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_4 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (41972593417413 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168446999033 / 50000000000000 : ℝ))
      (E := (cell12086 ⟨4, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (41972593417413 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168446999033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_5 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (41955054164989 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168448976659 / 50000000000000 : ℝ))
      (E := (cell12086 ⟨5, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (41955054164989 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168448976659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_6 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83875054901597 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (467380390063 / 20000000000000 : ℝ))
      (E := (cell12086 ⟨6, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83875054901597 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (467380390063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_7 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83840026513319 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336905940197 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨7, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83840026513319 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336905940197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_8 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (20951255782243 / 25000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168454965841 / 50000000000000 : ℝ))
      (E := (cell12086 ⟨8, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (20951255782243 / 25000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168454965841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_9 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (3350801788503 / 4000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (584228483307 / 25000000000000 : ℝ))
      (E := (cell12086 ⟨9, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (3350801788503 / 4000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (584228483307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_10 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (41867545614167 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (584229473767 / 25000000000000 : ℝ))
      (E := (cell12086 ⟨10, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (41867545614167 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (584229473767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_11 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (16740032528129 / 20000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336921883079 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨11, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (16740032528129 / 20000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336921883079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_12 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83665258914091 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (467385169387 / 20000000000000 : ℝ))
      (E := (cell12086 ⟨12, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83665258914091 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (467385169387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_13 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83630380013439 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168464926029 / 50000000000000 : ℝ))
      (E := (cell12086 ⟨13, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83630380013439 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168464926029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_14 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83595525903641 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336933847573 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨14, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83595525903641 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336933847573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_15 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (10445087068729 / 12500000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168468920177 / 50000000000000 : ℝ))
      (E := (cell12086 ⟨15, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (10445087068729 / 12500000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (1168468920177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_16 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83525891917331 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (73029432407 / 3125000000000 : ℝ))
      (E := (cell12086 ⟨16, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83525891917331 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (73029432407 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_17 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (41745555985817 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336945785823 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨17, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (41745555985817 / 50000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336945785823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_18 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83456356678419 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336949809139 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨18, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83456356678419 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336949809139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12086_19 : CellCertificate 12086 (904680719259899 / 10000000000000000 : ℝ) (1737943037420951 / 1000000000000000000 : ℝ) (351904676910511 / 10000000000000000 : ℝ)
    (cell12086 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · norm_num [cell12086]
  · have h := gap_lower (n := 12086) (a := (83421626003543 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336953796553 / 100000000000000 : ℝ))
      (E := (cell12086 ⟨19, by decide⟩).energy) (xi := (351904676910511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12086 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12086) (a := (83421626003543 / 100000000000000 : ℝ)) (b := (85318110499 / 50000000000000 : ℝ)) (q := (2336953796553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12086]

theorem cert12087_0 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (10510716955827 / 12500000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336712855101 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨0, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (10510716955827 / 12500000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336712855101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_1 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (8405055681391 / 10000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (292089604189 / 12500000000000 : ℝ))
      (E := (cell12087 ⟨1, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (8405055681391 / 10000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (292089604189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_2 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (42007701602289 / 50000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (584180203947 / 25000000000000 : ℝ))
      (E := (cell12087 ⟨2, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (42007701602289 / 50000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (584180203947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_3 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (41990137390739 / 50000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336724812017 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨3, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (41990137390739 / 50000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336724812017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_4 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (16789034301533 / 20000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336728832023 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨4, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (16789034301533 / 20000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336728832023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_5 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83910093346387 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336732769657 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨5, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83910093346387 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336732769657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_6 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (8387504026109 / 10000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (584184201931 / 25000000000000 : ℝ))
      (E := (cell12087 ⟨6, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (8387504026109 / 10000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (584184201931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_7 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (8384001221541 / 10000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (18693926253 / 800000000000 : ℝ))
      (E := (cell12087 ⟨7, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (8384001221541 / 10000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (18693926253 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_8 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (10475626146647 / 12500000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (467348951587 / 20000000000000 : ℝ))
      (E := (cell12087 ⟨8, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (10475626146647 / 12500000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (467348951587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_9 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83770031098407 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336748745113 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨9, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83770031098407 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336748745113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_10 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (5233442372207 / 6250000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (1168376375681 / 50000000000000 : ℝ))
      (E := (cell12087 ⟨10, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (5233442372207 / 6250000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (1168376375681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_11 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (163476854899 / 195312500000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336756726633 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨11, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (163476854899 / 195312500000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336756726633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_12 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83665246321917 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336760678553 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨12, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83665246321917 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336760678553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_13 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (10453795970121 / 12500000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (116838233627 / 5000000000000 : ℝ))
      (E := (cell12087 ⟨13, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (10453795970121 / 12500000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (116838233627 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_14 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (16719102798079 / 20000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336768657719 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨14, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (16719102798079 / 20000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336768657719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_15 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83560684975333 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (1168386320481 / 50000000000000 : ℝ))
      (E := (cell12087 ⟨15, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83560684975333 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (1168386320481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_16 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83525880681101 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (467355325779 / 20000000000000 : ℝ))
      (E := (cell12087 ⟨16, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83525880681101 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (467355325779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_17 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83491101073199 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (584195156973 / 25000000000000 : ℝ))
      (E := (cell12087 ⟨17, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83491101073199 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (584195156973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_18 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83456346117303 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336784644087 / 100000000000000 : ℝ))
      (E := (cell12087 ⟨18, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83456346117303 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (2336784644087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12087_19 : CellCertificate 12087 (452324994347493 / 5000000000000000 : ℝ) (217224900201423 / 125000000000000000 : ℝ) (43984353429129 / 1250000000000000 : ℝ)
    (cell12087 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · norm_num [cell12087]
  · have h := gap_lower (n := 12087) (a := (83421615779273 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (1168394312587 / 50000000000000 : ℝ))
      (E := (cell12087 ⟨19, by decide⟩).energy) (xi := (43984353429129 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12087 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12087) (a := (83421615779273 / 100000000000000 : ℝ)) (b := (6824877017 / 4000000000000 : ℝ)) (q := (1168394312587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12087]

theorem cert12088_0 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (84085718943047 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336547819733 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨0, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (84085718943047 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336547819733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_1 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (42025270227913 / 50000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336551835117 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨1, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (42025270227913 / 50000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336551835117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_2 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (84015387191489 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (1168277898717 / 50000000000000 : ℝ))
      (E := (cell12088 ⟨2, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (84015387191489 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (1168277898717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_3 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (83980259112893 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336559774517 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨3, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (83980259112893 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336559774517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_4 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (16789031236619 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336563776187 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨4, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (16789031236619 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336563776187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_5 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (2622189948917 / 3125000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336567754151 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨5, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (2622189948917 / 3125000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336567754151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_6 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (83875025623087 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336571775523 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨6, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (83875025623087 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336571775523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_7 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (2095999947999 / 2500000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (73017991673 / 3125000000000 : ℝ))
      (E := (cell12088 ⟨7, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (2095999947999 / 2500000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (73017991673 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_8 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (16760999043959 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (584144938173 / 25000000000000 : ℝ))
      (E := (cell12088 ⟨8, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (16760999043959 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (584144938173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_9 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (20942504371653 / 25000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (467316745123 / 20000000000000 : ℝ))
      (E := (cell12088 ⟨9, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (20942504371653 / 25000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (467316745123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_10 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (83735064684619 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (467317543683 / 20000000000000 : ℝ))
      (E := (cell12088 ⟨10, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (83735064684619 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (467317543683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_11 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (16740027355643 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336591681039 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨11, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (16740027355643 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336591681039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_12 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (5229077108249 / 6250000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (73018614973 / 3125000000000 : ℝ))
      (E := (cell12088 ⟨12, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (5229077108249 / 6250000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (73018614973 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_13 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (16726071102139 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336599662103 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨13, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (16726071102139 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336599662103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_14 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (83595502079303 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336603637061 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨14, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (83595502079303 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336603637061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_15 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (16712134680589 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (146037979311 / 6250000000000 : ℝ))
      (E := (cell12088 ⟨15, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (16712134680589 / 20000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (146037979311 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_16 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (83525869446941 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336611648307 / 100000000000000 : ℝ))
      (E := (cell12088 ⟨16, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (83525869446941 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (2336611648307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_17 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (83491090176789 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (1168307819751 / 50000000000000 : ℝ))
      (E := (cell12088 ⟨17, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (83491090176789 / 100000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (1168307819751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_18 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (8345633555817 / 10000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (93464783621 / 4000000000000 : ℝ))
      (E := (cell12088 ⟨18, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (8345633555817 / 10000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (93464783621 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12088_19 : CellCertificate 12088 (45230963151809 / 500000000000000 : ℝ) (34753107792163 / 20000000000000000 : ℝ) (351844983182563 / 10000000000000000 : ℝ)
    (cell12088 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · norm_num [cell12088]
  · have h := gap_lower (n := 12088) (a := (41710802778471 / 50000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (1168311782689 / 50000000000000 : ℝ))
      (E := (cell12088 ⟨19, by decide⟩).energy) (xi := (351844983182563 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12088 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12088) (a := (41710802778471 / 50000000000000 : ℝ)) (b := (170607632287 / 100000000000000 : ℝ)) (q := (1168311782689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12088]

theorem cert12089_0 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (16817140448449 / 20000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168191475973 / 50000000000000 : ℝ))
      (E := (cell12089 ⟨0, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (16817140448449 / 20000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168191475973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_1 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (42025262050233 / 50000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (584096736663 / 25000000000000 : ℝ))
      (E := (cell12089 ⟨1, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (42025262050233 / 50000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (584096736663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_2 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (42007685590539 / 50000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336390946893 / 100000000000000 : ℝ))
      (E := (cell12089 ⟨2, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (42007685590539 / 50000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336390946893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_3 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (83980243446943 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (146024681559 / 6250000000000 : ℝ))
      (E := (cell12089 ⟨3, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (83980243446943 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (146024681559 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_4 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (16789028172223 / 20000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168199444197 / 50000000000000 : ℝ))
      (E := (cell12089 ⟨4, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (16789028172223 / 20000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168199444197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_5 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (2622189480839 / 3125000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (467280581361 / 20000000000000 : ℝ))
      (E := (cell12089 ⟨5, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (2622189480839 / 3125000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (467280581361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_6 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (41937505493793 / 50000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (467281370743 / 20000000000000 : ℝ))
      (E := (cell12089 ⟨6, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (41937505493793 / 50000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (467281370743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_7 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (8383998362697 / 10000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336410853837 / 100000000000000 : ℝ))
      (E := (cell12089 ⟨7, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (8383998362697 / 10000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336410853837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_8 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (8380498126883 / 10000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168207429013 / 50000000000000 : ℝ))
      (E := (cell12089 ⟨8, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (8380498126883 / 10000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168207429013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_9 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (20942500969297 / 25000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336418816787 / 100000000000000 : ℝ))
      (E := (cell12089 ⟨9, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (20942500969297 / 25000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336418816787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_10 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (16747010283251 / 20000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336422796227 / 100000000000000 : ℝ))
      (E := (cell12089 ⟨10, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (16747010283251 / 20000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336422796227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_11 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (20925030962607 / 25000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (467285360859 / 20000000000000 : ℝ))
      (E := (cell12089 ⟨11, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (20925030962607 / 25000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (467285360859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_12 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (83665221144293 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336430790663 / 100000000000000 : ℝ))
      (E := (cell12089 ⟨12, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (83665221144293 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336430790663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_13 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (83630343262621 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (23364347627 / 1000000000000 : ℝ))
      (E := (cell12089 ⟨13, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (83630343262621 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (23364347627 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_14 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (83595490170367 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336438785599 / 100000000000000 : ℝ))
      (E := (cell12089 ⟨14, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (83595490170367 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336438785599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_15 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (83560661832669 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168221375057 / 50000000000000 : ℝ))
      (E := (cell12089 ⟨15, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (83560661832669 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168221375057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_16 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (1305091534607 / 1562500000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168223360457 / 50000000000000 : ℝ))
      (E := (cell12089 ⟨16, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (1305091534607 / 1562500000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168223360457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_17 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (20872769820601 / 25000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168225352187 / 50000000000000 : ℝ))
      (E := (cell12089 ⟨17, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (20872769820601 / 25000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168225352187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_18 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (83456325001019 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336454706621 / 100000000000000 : ℝ))
      (E := (cell12089 ⟨18, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (83456325001019 / 100000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (2336454706621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12089_19 : CellCertificate 12089 (3618354169129 / 40000000000000 : ℝ) (1737511601405339 / 1000000000000000000 : ℝ) (351815144157513 / 10000000000000000 : ℝ)
    (cell12089 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · norm_num [cell12089]
  · have h := gap_lower (n := 12089) (a := (1668431906731 / 2000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168229337677 / 50000000000000 : ℝ))
      (E := (cell12089 ⟨19, by decide⟩).energy) (xi := (351815144157513 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12089 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12089) (a := (1668431906731 / 2000000000000 : ℝ)) (b := (170593341583 / 100000000000000 : ℝ)) (q := (1168229337677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12089]

theorem cert12090_0 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (84085685544209 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336218193999 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨0, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (84085685544209 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336218193999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_1 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (84050507747827 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (58405554203 / 2500000000000 : ℝ))
      (E := (cell12090 ⟨1, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (84050507747827 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (58405554203 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_2 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (42007677586673 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (584056537147 / 25000000000000 : ℝ))
      (E := (cell12090 ⟨2, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (42007677586673 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (584056537147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_3 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (83980227783627 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (146014384093 / 6250000000000 : ℝ))
      (E := (cell12090 ⟨3, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (83980227783627 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (146014384093 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_4 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (41972562770863 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (233623411081 / 10000000000000 : ℝ))
      (E := (cell12090 ⟨4, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (41972562770863 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (233623411081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_5 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (41955024205449 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (1168119055951 / 50000000000000 : ℝ))
      (E := (cell12090 ⟨5, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (41955024205449 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (1168119055951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_6 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (20968749088647 / 25000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336242100183 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨6, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (20968749088647 / 25000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336242100183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_7 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (83839969336439 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336246084623 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨7, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (83839969336439 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336246084623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_8 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (2095124183007 / 2500000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336250073937 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨8, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (2095124183007 / 2500000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336250073937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_9 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (10471248783767 / 12500000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336254076581 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨9, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (10471248783767 / 12500000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336254076581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_10 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (83735038150217 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336258042779 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨10, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (83735038150217 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336258042779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_11 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (20925027731231 / 25000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336262038407 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨11, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (20925027731231 / 25000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336262038407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_12 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (41832604279421 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (467253202627 / 20000000000000 : ℝ))
      (E := (cell12090 ⟨12, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (41832604279421 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (467253202627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_13 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (83630331016743 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (1168135016191 / 50000000000000 : ℝ))
      (E := (cell12090 ⟨13, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (83630331016743 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (1168135016191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_14 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (2612358695737 / 3125000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336273987197 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨14, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (2612358695737 / 3125000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336273987197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_15 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (83560650264503 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336278000567 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨15, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (83560650264503 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336278000567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_16 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (41762923492411 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (46725639259 / 2000000000000 : ℝ))
      (E := (cell12090 ⟨16, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (41762923492411 / 50000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (46725639259 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_17 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (20872767097511 / 25000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336285996929 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨17, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (20872767097511 / 25000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336285996929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_18 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (10432039305731 / 12500000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336289934213 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨18, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (10432039305731 / 12500000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336289934213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12090_19 : CellCertificate 12090 (904557826431967 / 10000000000000000 : ℝ) (347473567399409 / 200000000000000000 : ℝ) (35178531035629 / 1000000000000000 : ℝ)
    (cell12090 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · norm_num [cell12090]
  · have h := gap_lower (n := 12090) (a := (83421585118097 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336293955103 / 100000000000000 : ℝ))
      (E := (cell12090 ⟨19, by decide⟩).energy) (xi := (35178531035629 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12090 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12090) (a := (83421585118097 / 100000000000000 : ℝ)) (b := (170579053313 / 100000000000000 : ℝ)) (q := (2336293955103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12090]

theorem cert12091_0 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (84085668848939 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (467210709179 / 20000000000000 : ℝ))
      (E := (cell12091 ⟨0, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (84085668848939 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (467210709179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_1 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (8405049139791 / 10000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (292007194661 / 12500000000000 : ℝ))
      (E := (cell12091 ⟨1, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (8405049139791 / 10000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (292007194661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_2 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (84015339168291 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336061518099 / 100000000000000 : ℝ))
      (E := (cell12091 ⟨2, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (84015339168291 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336061518099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_3 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (1312190814421 / 1562500000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (467213110793 / 20000000000000 : ℝ))
      (E := (cell12091 ⟨3, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (1312190814421 / 1562500000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (467213110793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_4 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (41972555112463 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168034750637 / 50000000000000 : ℝ))
      (E := (cell12091 ⟨4, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (41972555112463 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168034750637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_5 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (83910033437493 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168036742581 / 50000000000000 : ℝ))
      (E := (cell12091 ⟨5, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (83910033437493 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168036742581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_6 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (20968745431023 / 25000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (233607751493 / 10000000000000 : ℝ))
      (E := (cell12091 ⟨6, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (20968745431023 / 25000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (233607751493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_7 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (16767991009673 / 20000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (584020370951 / 25000000000000 : ℝ))
      (E := (cell12091 ⟨7, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (16767991009673 / 20000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (584020370951 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_8 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (16760990674829 / 20000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168042729179 / 50000000000000 : ℝ))
      (E := (cell12091 ⟨8, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (16760990674829 / 20000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168042729179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_9 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (41884988332727 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (292011180881 / 12500000000000 : ℝ))
      (E := (cell12091 ⟨9, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (41884988332727 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (292011180881 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_10 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (83735024886507 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336093458071 / 100000000000000 : ℝ))
      (E := (cell12091 ⟨10, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (83735024886507 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336093458071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_11 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (10462512250213 / 12500000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168048720687 / 50000000000000 : ℝ))
      (E := (cell12091 ⟨11, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (10462512250213 / 12500000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168048720687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_12 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (83665195975631 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (116805070229 / 5000000000000 : ℝ))
      (E := (cell12091 ⟨12, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (83665195975631 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (116805070229 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_13 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (41815159386531 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (146006588319 / 6250000000000 : ℝ))
      (E := (cell12091 ⟨13, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (41815159386531 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (146006588319 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_14 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (41797733179477 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336109416067 / 100000000000000 : ℝ))
      (E := (cell12091 ⟨14, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (41797733179477 / 50000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336109416067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_15 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (83560638698447 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336113362243 / 100000000000000 : ℝ))
      (E := (cell12091 ⟨15, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (83560638698447 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336113362243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_16 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (1305091183701 / 1562500000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336117374417 / 100000000000000 : ℝ))
      (E := (cell12091 ⟨16, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (1305091183701 / 1562500000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336117374417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_17 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (83491057499707 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336121342751 / 100000000000000 : ℝ))
      (E := (cell12091 ⟨17, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (83491057499707 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (2336121342751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_18 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (83456303892659 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (467225066293 / 20000000000000 : ℝ))
      (E := (cell12091 ⟨18, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (83456303892659 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (467225066293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12091_19 : CellCertificate 12091 (904527115484101 / 10000000000000000 : ℝ) (1737224096377361 / 1000000000000000000 : ℝ) (43969435222163 / 1250000000000000 : ℝ)
    (cell12091 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · norm_num [cell12091]
  · have h := gap_lower (n := 12091) (a := (83421574901581 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168064673221 / 50000000000000 : ℝ))
      (E := (cell12091 ⟨19, by decide⟩).energy) (xi := (43969435222163 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12091 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12091) (a := (83421574901581 / 100000000000000 : ℝ)) (b := (42641191869 / 25000000000000 : ℝ)) (q := (1168064673221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12091]

theorem cert12092_0 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (42042826078217 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335889065377 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨0, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (42042826078217 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335889065377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_1 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (42025237525357 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167946528197 / 50000000000000 : ℝ))
      (E := (cell12092 ⟨1, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (42025237525357 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167946528197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_2 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (42007661582957 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335897055427 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨2, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (42007661582957 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335897055427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_3 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (41990098232447 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583975268141 / 25000000000000 : ℝ))
      (E := (cell12092 ⟨3, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (41990098232447 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583975268141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_4 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (20986273727679 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583976264947 / 25000000000000 : ℝ))
      (E := (cell12092 ⟨4, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (20986273727679 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583976264947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_5 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (83910018466633 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335909026589 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨5, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (83910018466633 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335909026589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_6 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (83874967096097 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (93436521603 / 4000000000000 : ℝ))
      (E := (cell12092 ⟨6, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (83874967096097 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (93436521603 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_7 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (20959985190687 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335916993477 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨7, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (20959985190687 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335916993477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_8 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (41902469715211 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335921011293 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨8, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (41902469715211 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335921011293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_9 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (83769963063143 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167962493071 / 50000000000000 : ℝ))
      (E := (cell12092 ⟨9, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (83769963063143 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167962493071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_10 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (20933752906281 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335928984129 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨10, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (20933752906281 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335928984129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_11 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (83700085080767 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335932955199 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨11, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (83700085080767 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335932955199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_12 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (4183259169733 / 5000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167968453487 / 50000000000000 : ℝ))
      (E := (cell12092 ⟨12, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (4183259169733 / 5000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167968453487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_13 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (41815153265789 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583985226217 / 25000000000000 : ℝ))
      (E := (cell12092 ⟨13, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (41815153265789 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583985226217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_14 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (41797727228239 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335944897999 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨14, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (41797727228239 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335944897999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_15 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (83560627134501 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167974446619 / 50000000000000 : ℝ))
      (E := (cell12092 ⟨15, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (83560627134501 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167974446619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_16 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (20881456132743 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335952897201 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨16, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (20881456132743 / 25000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335952897201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_17 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (83491046611393 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167978429061 / 50000000000000 : ℝ))
      (E := (cell12092 ⟨17, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (83491046611393 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (1167978429061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_18 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (83456293341449 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335960840219 / 100000000000000 : ℝ))
      (E := (cell12092 ⟨18, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (83456293341449 / 100000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (2335960840219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12092_19 : CellCertificate 12092 (36179856377497 / 400000000000000 : ℝ) (1737080379540383 / 1000000000000000000 : ℝ) (43965707302371 / 1250000000000000 : ℝ)
    (cell12092 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · norm_num [cell12092]
  · have h := gap_lower (n := 12092) (a := (41710782343501 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583991212343 / 25000000000000 : ℝ))
      (E := (cell12092 ⟨19, by decide⟩).energy) (xi := (43965707302371 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12092 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12092) (a := (41710782343501 / 50000000000000 : ℝ)) (b := (170550484071 / 100000000000000 : ℝ)) (q := (583991212343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12092]

theorem cert12093_0 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (84085635466693 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (46714495049 / 2000000000000 : ℝ))
      (E := (cell12093 ⟨0, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (84085635466693 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (46714495049 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_1 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (84050458706239 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583932180801 / 25000000000000 : ℝ))
      (E := (cell12093 ⟨1, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (84050458706239 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583932180801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_2 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (21003826791553 / 25000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335732702789 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨2, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (21003826791553 / 25000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335732702789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_3 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (20995045202369 / 25000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335736701289 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨3, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (20995045202369 / 25000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335736701289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_4 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (83945079599093 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583935167671 / 25000000000000 : ℝ))
      (E := (cell12093 ⟨4, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (83945079599093 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583935167671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_5 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (41955001749159 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583936169581 / 25000000000000 : ℝ))
      (E := (cell12093 ⟨5, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (41955001749159 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583936169581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_6 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (41937476235301 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335748675623 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨6, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (41937476235301 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335748675623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_7 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (83839926479589 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335752671549 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨7, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (83839926479589 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335752671549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_8 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (83804925489113 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335756616883 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨8, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (83804925489113 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335756616883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_9 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (104712436829 / 125000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (467152127183 / 20000000000000 : ℝ))
      (E := (cell12093 ⟨9, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (104712436829 / 125000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (467152127183 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_10 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (41867499183033 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (1167882310479 / 50000000000000 : ℝ))
      (E := (cell12093 ⟨10, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (41867499183033 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (1167882310479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_11 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (1307813627533 / 1562500000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335768579887 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨11, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (1307813627533 / 1562500000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335768579887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_12 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (10458146351991 / 12500000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (467154515669 / 20000000000000 : ℝ))
      (E := (cell12093 ⟨12, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (10458146351991 / 12500000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (467154515669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_13 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (1306723348317 / 1562500000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583944141431 / 25000000000000 : ℝ))
      (E := (cell12093 ⟨13, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (1306723348317 / 1562500000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583944141431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_14 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (83595442556153 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (116789027457 / 5000000000000 : ℝ))
      (E := (cell12093 ⟨14, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (83595442556153 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (116789027457 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_15 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (10445076946583 / 12500000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335784535461 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨15, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (10445076946583 / 12500000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335784535461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_16 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (41762906653573 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (467157706261 / 20000000000000 : ℝ))
      (E := (cell12093 ⟨16, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (41762906653573 / 50000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (467157706261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_17 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (83491035725103 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583948135761 / 25000000000000 : ℝ))
      (E := (cell12093 ⟨17, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (83491035725103 / 100000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (583948135761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_18 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (4172814139611 / 5000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335796518637 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨18, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (4172814139611 / 5000000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335796518637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12093_19 : CellCertificate 12093 (904465708290709 / 10000000000000000 : ℝ) (1736936686480209 / 1000000000000000000 : ℝ) (87923960069923 / 2500000000000000 : ℝ)
    (cell12093 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · norm_num [cell12093]
  · have h := gap_lower (n := 12093) (a := (2085538861859 / 2500000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335800522083 / 100000000000000 : ℝ))
      (E := (cell12093 ⟨19, by decide⟩).energy) (xi := (87923960069923 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12093 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12093) (a := (2085538861859 / 2500000000000 : ℝ)) (b := (170536203097 / 100000000000000 : ℝ)) (q := (2335800522083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12093]

theorem cert12094_0 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (84085618779717 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335560549371 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨0, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (84085618779717 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335560549371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_1 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (84050442364483 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335564499957 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨1, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (84050442364483 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335564499957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_2 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (42007645584593 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167784258987 / 50000000000000 : ℝ))
      (E := (cell12094 ⟨2, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (42007645584593 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167784258987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_3 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (8398016515669 / 10000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335572497951 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨3, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (8398016515669 / 10000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335572497951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_4 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (41972532145029 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (233557650747 / 10000000000000 : ℝ))
      (E := (cell12094 ⟨4, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (41972532145029 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (233557650747 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_5 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (41954994266273 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335580440371 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨5, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (41954994266273 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335580440371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_6 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (83874937847607 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335584479457 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨6, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (83874937847607 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335584479457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_7 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (16767982439777 / 20000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335588460117 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨7, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (16767982439777 / 20000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335588460117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_8 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (10475613943777 / 12500000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (58389811223 / 2500000000000 : ℝ))
      (E := (cell12094 ⟨8, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (10475613943777 / 12500000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (58389811223 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_9 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (83769935865627 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167798198183 / 50000000000000 : ℝ))
      (E := (cell12094 ⟨9, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (83769935865627 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167798198183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_10 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (83734985109333 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167800213267 / 50000000000000 : ℝ))
      (E := (cell12094 ⟨10, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (83734985109333 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167800213267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_11 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (41850029622869 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335604373437 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨11, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (41850029622869 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335604373437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_12 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (83665158239433 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335608360671 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨12, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (83665158239433 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335608360671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_13 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (41815141027597 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167806168813 / 50000000000000 : ℝ))
      (E := (cell12094 ⟨13, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (41815141027597 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (1167806168813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_14 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (4179771532899 / 5000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335616369489 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨14, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (4179771532899 / 5000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335616369489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_15 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (16712120802587 / 20000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (18247033961 / 781250000000 : ℝ))
      (E := (cell12094 ⟨15, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (16712120802587 / 20000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (18247033961 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_16 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (10440725260673 / 12500000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (4561766279 / 195312500000 : ℝ))
      (E := (cell12094 ⟨16, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (10440725260673 / 12500000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (4561766279 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_17 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (41745512420417 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335628339379 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨17, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (41745512420417 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335628339379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_18 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (83456272244969 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335632308561 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨18, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (83456272244969 / 100000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335632308561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12094_19 : CellCertificate 12094 (452217506021363 / 5000000000000000 : ℝ) (1736793017190939 / 1000000000000000000 : ℝ) (351666027357889 / 10000000000000000 : ℝ)
    (cell12094 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · norm_num [cell12094]
  · have h := gap_lower (n := 12094) (a := (41710772131827 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335636306389 / 100000000000000 : ℝ))
      (E := (cell12094 ⟨19, by decide⟩).energy) (xi := (351666027357889 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12094 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12094) (a := (41710772131827 / 50000000000000 : ℝ)) (b := (85260962277 / 50000000000000 : ℝ)) (q := (2335636306389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12094]

theorem cert12095_0 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (84085602095503 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335396456143 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨0, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (84085602095503 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335396456143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_1 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (42025213012723 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335400444419 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨1, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (42025213012723 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335400444419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_2 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (42007637587417 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583851110799 / 25000000000000 : ℝ))
      (E := (cell12095 ⟨2, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (42007637587417 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583851110799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_3 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (41990074753267 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (1167704202371 / 50000000000000 : ℝ))
      (E := (cell12095 ⟨3, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (41990074753267 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (1167704202371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_4 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83945048983609 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335412396641 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨4, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83945048983609 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335412396641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_5 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (41954986784659 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583854092647 / 25000000000000 : ℝ))
      (E := (cell12095 ⟨5, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (41954986784659 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583854092647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_6 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (10484365403389 / 12500000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (1167710196847 / 50000000000000 : ℝ))
      (E := (cell12095 ⟨6, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (10484365403389 / 12500000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (1167710196847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_7 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83839897920637 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (116771217959 / 5000000000000 : ℝ))
      (E := (cell12095 ⟨7, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83839897920637 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (116771217959 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_8 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83804897613731 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (145964270851 / 6250000000000 : ℝ))
      (E := (cell12095 ⟨8, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83804897613731 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (145964270851 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_9 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83769922270421 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335432325451 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨9, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83769922270421 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335432325451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_10 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (3349398874197 / 4000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335436342883 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨10, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (3349398874197 / 4000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335436342883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_11 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (41850023165823 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583860083963 / 25000000000000 : ℝ))
      (E := (cell12095 ⟨11, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (41850023165823 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583860083963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_12 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83665145665177 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335444311977 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨12, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83665145665177 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335444311977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_13 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (41815134910147 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335448278623 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨13, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (41815134910147 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335448278623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_14 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (41797709380979 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335452300977 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨14, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (41797709380979 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335452300977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_15 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (41780296227657 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (467091253957 / 20000000000000 : ℝ))
      (E := (cell12095 ⟨15, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (41780296227657 / 50000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (467091253957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_16 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (10440723858211 / 12500000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (145966265607 / 6250000000000 : ℝ))
      (E := (cell12095 ⟨16, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (10440723858211 / 12500000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (145966265607 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_17 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83491013958587 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335464247127 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨17, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83491013958587 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335464247127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_18 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83456261699697 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583867052497 / 25000000000000 : ℝ))
      (E := (cell12095 ⟨18, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83456261699697 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (583867052497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12095_19 : CellCertificate 12095 (113050540086531 / 1250000000000000 : ℝ) (434162342916669 / 250000000000000000 : ℝ) (351636219651973 / 10000000000000000 : ℝ)
    (cell12095 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · norm_num [cell12095]
  · have h := gap_lower (n := 12095) (a := (83421534054883 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335472202291 / 100000000000000 : ℝ))
      (E := (cell12095 ⟨19, by decide⟩).energy) (xi := (351636219651973 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12095 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12095) (a := (83421534054883 / 100000000000000 : ℝ)) (b := (85253824221 / 50000000000000 : ℝ)) (q := (2335472202291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12095]

theorem cert12096_0 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (21021396353513 / 25000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (145952033157 / 6250000000000 : ℝ))
      (E := (cell12096 ⟨0, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (21021396353513 / 25000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (145952033157 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_1 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (84050409689127 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335236498827 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨1, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (84050409689127 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335236498827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_2 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (84015259183157 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (291905059807 / 12500000000000 : ℝ))
      (E := (cell12096 ⟨2, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (84015259183157 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (291905059807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_3 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83980133859009 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335244479477 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨3, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83980133859009 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335244479477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_4 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83945033679747 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (145953028367 / 6250000000000 : ℝ))
      (E := (cell12096 ⟨4, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83945033679747 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (145953028367 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_5 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83909958608631 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335252468983 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨5, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83909958608631 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335252468983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_6 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (41937454304557 / 50000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335256418341 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨6, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (41937454304557 / 50000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335256418341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_7 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (20959970911211 / 25000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335260426651 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨7, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (20959970911211 / 25000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335260426651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_8 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83804883679657 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335264386833 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨8, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83804883679657 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335264386833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_9 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (5235619292349 / 6250000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (1167634211587 / 50000000000000 : ℝ))
      (E := (cell12096 ⟨9, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (5235619292349 / 6250000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (1167634211587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_10 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83734958602841 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335272370007 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨10, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83734958602841 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335272370007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_11 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (16740006683967 / 20000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335276351133 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨11, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (16740006683967 / 20000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335276351133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_12 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (41832566546579 / 50000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335280374241 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨12, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (41832566546579 / 50000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335280374241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_13 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (20907564396897 / 25000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (233528433067 / 10000000000000 : ℝ))
      (E := (cell12096 ⟨13, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (20907564396897 / 25000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (233528433067 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_14 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83595406868087 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335288343607 / 100000000000000 : ℝ))
      (E := (cell12096 ⟨14, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83595406868087 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (2335288343607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_15 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83560580899801 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (583823075949 / 25000000000000 : ℝ))
      (E := (cell12096 ⟨15, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83560580899801 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (583823075949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_16 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (10440722456007 / 12500000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (116764816701 / 5000000000000 : ℝ))
      (E := (cell12096 ⟨16, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (10440722456007 / 12500000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (116764816701 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_17 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83491003078361 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (1167650162217 / 50000000000000 : ℝ))
      (E := (cell12096 ⟨17, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83491003078361 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (1167650162217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_18 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (83456251156403 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (233530428109 / 10000000000000 : ℝ))
      (E := (cell12096 ⟨18, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (83456251156403 / 100000000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (233530428109 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12096_19 : CellCertificate 12096 (904373634238049 / 10000000000000000 : ℝ) (868252874950761 / 500000000000000000 : ℝ) (351606417160359 / 10000000000000000 : ℝ)
    (cell12096 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · norm_num [cell12096]
  · have h := gap_lower (n := 12096) (a := (5213845240503 / 6250000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (1167654133991 / 50000000000000 : ℝ))
      (E := (cell12096 ⟨19, by decide⟩).energy) (xi := (351606417160359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12096 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12096) (a := (5213845240503 / 6250000000000 : ℝ)) (b := (170493374759 / 100000000000000 : ℝ)) (q := (1167654133991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12096]

theorem cert12097_0 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (42042784367681 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (145941794671 / 6250000000000 : ℝ))
      (E := (cell12097 ⟨0, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (42042784367681 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (145941794671 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_1 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (3362015734221 / 4000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (46701454419 / 2000000000000 : ℝ))
      (E := (cell12097 ⟨1, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (3362015734221 / 4000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (46701454419 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_2 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (84015243194153 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467015336309 / 20000000000000 : ℝ))
      (E := (cell12097 ⟨2, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (84015243194153 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467015336309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_3 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (83980118214113 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467016132869 / 20000000000000 : ℝ))
      (E := (cell12097 ⟨3, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (83980118214113 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467016132869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_4 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (83945018378471 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167542339581 / 50000000000000 : ℝ))
      (E := (cell12097 ⟨4, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (83945018378471 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167542339581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_5 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (41954971825243 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167544309917 / 50000000000000 : ℝ))
      (E := (cell12097 ⟨5, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (41954971825243 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167544309917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_6 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (16774978798723 / 20000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167546305639 / 50000000000000 : ℝ))
      (E := (cell12097 ⟨6, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (16774978798723 / 20000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167546305639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_7 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (5239991835719 / 6250000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335096604623 / 100000000000000 : ℝ))
      (E := (cell12097 ⟨7, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (5239991835719 / 6250000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335096604623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_8 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (41902434873997 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167550304287 / 50000000000000 : ℝ))
      (E := (cell12097 ⟨8, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (41902434873997 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167550304287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_9 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (83769895087113 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335104573627 / 100000000000000 : ℝ))
      (E := (cell12097 ⟨9, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (83769895087113 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335104573627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_10 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (2093373633827 / 2500000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467021713177 / 20000000000000 : ℝ))
      (E := (cell12097 ⟨10, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (2093373633827 / 2500000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467021713177 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_11 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (83700020510303 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467022518657 / 20000000000000 : ℝ))
      (E := (cell12097 ⟨11, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (83700020510303 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (467022518657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_12 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (669320964187 / 800000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167558273733 / 50000000000000 : ℝ))
      (E := (cell12097 ⟨12, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (669320964187 / 800000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167558273733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_13 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (3345209814283 / 4000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335120551817 / 100000000000000 : ℝ))
      (E := (cell12097 ⟨13, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (3345209814283 / 4000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335120551817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_14 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (41797697488183 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335124555451 / 100000000000000 : ℝ))
      (E := (cell12097 ⟨14, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (41797697488183 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335124555451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_15 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (41780284673197 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (9121595731 / 390625000000 : ℝ))
      (E := (cell12097 ⟨15, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (41780284673197 / 50000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (9121595731 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_16 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (10440721054061 / 12500000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167566264827 / 50000000000000 : ℝ))
      (E := (cell12097 ⟨16, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (10440721054061 / 12500000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167566264827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_17 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (20872748050039 / 25000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167568256579 / 50000000000000 : ℝ))
      (E := (cell12097 ⟨17, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (20872748050039 / 25000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (1167568256579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_18 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (83456240615087 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335140463699 / 100000000000000 : ℝ))
      (E := (cell12097 ⟨18, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (83456240615087 / 100000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335140463699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12097_19 : CellCertificate 12097 (904342952678901 / 10000000000000000 : ℝ) (108522634493099 / 62500000000000000 : ℝ) (175788309940731 / 5000000000000000 : ℝ)
    (cell12097 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · norm_num [cell12097]
  · have h := gap_lower (n := 12097) (a := (20855378410787 / 25000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335144445271 / 100000000000000 : ℝ))
      (E := (cell12097 ⟨19, by decide⟩).energy) (xi := (175788309940731 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12097 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12097) (a := (20855378410787 / 25000000000000 : ℝ)) (b := (85239551753 / 50000000000000 : ℝ)) (q := (2335144445271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12097]

theorem cert12098_0 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (84085552059433 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (116745250441 / 5000000000000 : ℝ))
      (E := (cell12098 ⟨0, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (84085552059433 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (116745250441 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_1 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (84050377024641 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167454497629 / 50000000000000 : ℝ))
      (E := (cell12098 ⟨1, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (84050377024641 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167454497629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_2 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (42007613603911 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334912994679 / 100000000000000 : ℝ))
      (E := (cell12098 ⟨2, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (42007613603911 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334912994679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_3 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (41990051285923 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167458508581 / 50000000000000 : ℝ))
      (E := (cell12098 ⟨3, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (41990051285923 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167458508581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_4 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83945003079779 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167460478423 / 50000000000000 : ℝ))
      (E := (cell12098 ⟨4, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83945003079779 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167460478423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_5 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83909928694883 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (466984987773 / 20000000000000 : ℝ))
      (E := (cell12098 ⟨5, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83909928694883 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (466984987773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_6 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83874879380613 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334928972513 / 100000000000000 : ℝ))
      (E := (cell12098 ⟨6, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83874879380613 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334928972513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_7 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83839855100619 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167466475503 / 50000000000000 : ℝ))
      (E := (cell12098 ⟨7, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83839855100619 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (1167466475503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_8 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (4190242790937 / 5000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (145933558807 / 6250000000000 : ℝ))
      (E := (cell12098 ⟨8, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (4190242790937 / 5000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (145933558807 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_9 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (654452199211 / 781250000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583735223181 / 25000000000000 : ℝ))
      (E := (cell12098 ⟨9, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (654452199211 / 781250000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583735223181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_10 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (41867466052821 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334944930521 / 100000000000000 : ℝ))
      (E := (cell12098 ⟨10, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (41867466052821 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334944930521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_11 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83700007603051 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583737222077 / 25000000000000 : ℝ))
      (E := (cell12098 ⟨11, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83700007603051 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583737222077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_12 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83665107955829 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334952889679 / 100000000000000 : ℝ))
      (E := (cell12098 ⟨12, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83665107955829 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334952889679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_13 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (16726046625751 / 20000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (116747844201 / 5000000000000 : ℝ))
      (E := (cell12098 ⟨13, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (16726046625751 / 20000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (116747844201 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_14 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (41797691543397 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334960878443 / 100000000000000 : ℝ))
      (E := (cell12098 ⟨14, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (41797691543397 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334960878443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_15 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83560557795093 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583741205429 / 25000000000000 : ℝ))
      (E := (cell12098 ⟨15, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83560557795093 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583741205429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_16 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (41762878609491 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334968836619 / 100000000000000 : ℝ))
      (E := (cell12098 ⟨16, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (41762878609491 / 50000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (2334968836619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_17 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (8349098132397 / 10000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (291871601663 / 12500000000000 : ℝ))
      (E := (cell12098 ⟨17, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (8349098132397 / 10000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (291871601663 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_18 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83456230075747 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583744203997 / 25000000000000 : ℝ))
      (E := (cell12098 ⟨18, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83456230075747 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (583744203997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12098_19 : CellCertificate 12098 (452156138006789 / 5000000000000000 : ℝ) (1736218577624969 / 1000000000000000000 : ℝ) (175773413906849 / 5000000000000000 : ℝ)
    (cell12098 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · norm_num [cell12098]
  · have h := gap_lower (n := 12098) (a := (83421503440181 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (466996158471 / 20000000000000 : ℝ))
      (E := (cell12098 ⟨19, by decide⟩).energy) (xi := (175773413906849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12098 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12098) (a := (83421503440181 / 100000000000000 : ℝ)) (b := (4261620867 / 2500000000000 : ℝ)) (q := (466996158471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12098]

theorem cert12099_0 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (16817107077253 / 20000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334741470507 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨0, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (16817107077253 / 20000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334741470507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_1 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (84050360696473 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334745495051 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨1, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (84050360696473 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334745495051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_2 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (84015211224163 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (36480460557 / 1562500000000 : ℝ))
      (E := (cell12099 ⟨2, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (84015211224163 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (36480460557 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_3 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (83980086932207 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334753422303 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨3, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (83980086932207 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334753422303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_4 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (10493123472959 / 12500000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (145922341277 / 6250000000000 : ℝ))
      (E := (cell12099 ⟨4, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (10493123472959 / 12500000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (145922341277 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_5 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (4195495687091 / 5000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334761426079 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨5, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (4195495687091 / 5000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334761426079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_6 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (20968716192527 / 25000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334765386277 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨6, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (20968716192527 / 25000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334765386277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_7 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (41919920416093 / 50000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (466953881579 / 20000000000000 : ℝ))
      (E := (cell12099 ⟨7, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (41919920416093 / 50000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (466953881579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_8 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (10475605236487 / 12500000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334773383847 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨8, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (10475605236487 / 12500000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334773383847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_9 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (83769867913269 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (145923586279 / 6250000000000 : ℝ))
      (E := (cell12099 ⟨9, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (83769867913269 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (145923586279 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_10 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (83734918860527 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (58369533699 / 2500000000000 : ℝ))
      (E := (cell12099 ⟨10, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (83734918860527 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (58369533699 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_11 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (41849997349039 / 50000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (466957070441 / 20000000000000 : ℝ))
      (E := (cell12099 ⟨11, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (41849997349039 / 50000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (466957070441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_12 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (83665095390517 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (1167394671429 / 50000000000000 : ℝ))
      (E := (cell12099 ⟨12, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (83665095390517 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (1167394671429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_13 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (83630220902627 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334793327279 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨13, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (83630220902627 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334793327279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_14 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (83595371199371 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334797312583 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨14, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (83595371199371 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334797312583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_15 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (41780273122949 / 50000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (233480130563 / 10000000000000 : ℝ))
      (E := (cell12099 ⟨15, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (41780273122949 / 50000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (233480130563 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_16 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (83525746007539 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (291850664129 / 12500000000000 : ℝ))
      (E := (cell12099 ⟨16, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (83525746007539 / 100000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (291850664129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_17 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (16698194089961 / 20000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334809283013 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨17, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (16698194089961 / 20000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334809283013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_18 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (16691243907677 / 20000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334813279789 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨18, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (16691243907677 / 20000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334813279789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12099_19 : CellCertificate 12099 (113035200530107 / 1250000000000000 : ℝ) (434018756775447 / 250000000000000000 : ℝ) (70303408191097 / 2000000000000000 : ℝ)
    (cell12099 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · norm_num [cell12099]
  · have h := gap_lower (n := 12099) (a := (20855373309787 / 25000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334817251043 / 100000000000000 : ℝ))
      (E := (cell12099 ⟨19, by decide⟩).energy) (xi := (70303408191097 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12099 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12099) (a := (20855373309787 / 25000000000000 : ℝ)) (b := (85225284141 / 50000000000000 : ℝ)) (q := (2334817251043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12099]

theorem cert12100_0 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (5255344919741 / 6250000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334578099799 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨0, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (5255344919741 / 6250000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334578099799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_1 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (4202517218551 / 5000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334582047033 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨1, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (4202517218551 / 5000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334582047033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_2 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (10501899405397 / 12500000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334586066663 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨2, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (10501899405397 / 12500000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334586066663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_3 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (20995017823799 / 25000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (233459005321 / 10000000000000 : ℝ))
      (E := (cell12100 ⟨3, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (20995017823799 / 25000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (233459005321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_4 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (20986243122537 / 25000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167297008207 / 50000000000000 : ℝ))
      (E := (cell12100 ⟨4, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (20986243122537 / 25000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167297008207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_5 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (655546084307 / 781250000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334598023617 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨5, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (655546084307 / 781250000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334598023617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_6 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83874850162099 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (145912626639 / 6250000000000 : ℝ))
      (E := (cell12100 ⟨6, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83874850162099 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (145912626639 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_7 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (41919913283103 / 50000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (583651493823 / 25000000000000 : ℝ))
      (E := (cell12100 ⟨7, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (41919913283103 / 50000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (583651493823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_8 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83804827967461 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (145913124707 / 6250000000000 : ℝ))
      (E := (cell12100 ⟨8, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83804827967461 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (145913124707 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_9 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (10471231791237 / 12500000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (466922795779 / 20000000000000 : ℝ))
      (E := (cell12100 ⟨9, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (10471231791237 / 12500000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (466922795779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_10 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83734905617733 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334617934161 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨10, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83734905617733 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334617934161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_11 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83699981795383 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334621926977 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨11, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83699981795383 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334621926977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_12 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83665082827441 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167312953501 / 50000000000000 : ℝ))
      (E := (cell12100 ⟨12, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83665082827441 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167312953501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_13 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (8363020867869 / 10000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167314969823 / 50000000000000 : ℝ))
      (E := (cell12100 ⟨13, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (8363020867869 / 10000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167314969823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_14 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (5224709957131 / 6250000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (466926783189 / 20000000000000 : ℝ))
      (E := (cell12100 ⟨14, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (5224709957131 / 6250000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (466926783189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_15 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83560534698809 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (466927580157 / 20000000000000 : ℝ))
      (E := (cell12100 ⟨15, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83560534698809 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (466927580157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_16 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83525734798159 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334641900779 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨16, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83525734798159 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334641900779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_17 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (41745479788829 / 50000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (583661466037 / 25000000000000 : ℝ))
      (E := (cell12100 ⟨17, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (41745479788829 / 50000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (583661466037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_18 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (41728104501499 / 50000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167324927553 / 50000000000000 : ℝ))
      (E := (cell12100 ⟨18, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (41728104501499 / 50000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (1167324927553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12100_19 : CellCertificate 12100 (904250937359507 / 10000000000000000 : ℝ) (1735931500314151 / 1000000000000000000 : ℝ) (351487259305241 / 10000000000000000 : ℝ)
    (cell12100 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · norm_num [cell12100]
  · have h := gap_lower (n := 12100) (a := (83421483040049 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334653821337 / 100000000000000 : ℝ))
      (E := (cell12100 ⟨19, by decide⟩).energy) (xi := (351487259305241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12100 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12100]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12100])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12100) (a := (83421483040049 / 100000000000000 : ℝ)) (b := (170436304311 / 100000000000000 : ℝ)) (q := (2334653821337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12100])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12100]

theorem cert12101_0 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (84085502048207 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (583603695303 / 25000000000000 : ℝ))
      (E := (cell12101 ⟨0, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (84085502048207 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (583603695303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_1 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (42025164024141 / 50000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167209383369 / 50000000000000 : ℝ))
      (E := (cell12101 ⟨1, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (42025164024141 / 50000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167209383369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_2 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (4200758963243 / 5000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (145901422983 / 6250000000000 : ℝ))
      (E := (cell12101 ⟨2, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (4200758963243 / 5000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (145901422983 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_3 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (20995013915203 / 25000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334426794259 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨3, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (20995013915203 / 25000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334426794259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_4 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83944957199207 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334430740467 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨4, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83944957199207 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334430740467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_5 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (5244367740207 / 6250000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (58360868287 / 2500000000000 : ℝ))
      (E := (cell12101 ⟨5, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (5244367740207 / 6250000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (58360868287 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_6 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (16774967111317 / 20000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334438718707 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨6, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (16774967111317 / 20000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334438718707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_7 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83839812302677 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334442711107 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨7, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83839812302677 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334442711107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_8 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83804814045433 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334446717381 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨8, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83804814045433 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334446717381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_9 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (41884920374443 / 50000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167225344011 / 50000000000000 : ℝ))
      (E := (cell12101 ⟨9, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (41884920374443 / 50000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167225344011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_10 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (4186744618863 / 5000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167227344563 / 50000000000000 : ℝ))
      (E := (cell12101 ⟨10, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (4186744618863 / 5000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167227344563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_11 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (16739993778993 / 20000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334458670629 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨11, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (16739993778993 / 20000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334458670629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_12 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83665070266599 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334462640141 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨12, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83665070266599 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334462640141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_13 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (5226887278559 / 6250000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334466663073 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨13, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (5226887278559 / 6250000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334466663073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_14 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83595347430969 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334470630459 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨14, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83595347430969 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334470630459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_15 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83560523153823 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (466894921437 / 20000000000000 : ℝ))
      (E := (cell12101 ⟨15, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83560523153823 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (466894921437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_16 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83525723590839 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167239299931 / 50000000000000 : ℝ))
      (E := (cell12101 ⟨16, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83525723590839 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (1167239299931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_17 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (8349094870753 / 10000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334482614851 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨17, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (8349094870753 / 10000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334482614851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_18 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (83456198469587 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (583621650027 / 25000000000000 : ℝ))
      (E := (cell12101 ⟨18, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (83456198469587 / 100000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (583621650027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12101_19 : CellCertificate 12101 (226055068842077 / 2500000000000000 : ℝ) (1735787997256173 / 1000000000000000000 : ℝ) (43932185357673 / 1250000000000000 : ℝ)
    (cell12101 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · norm_num [cell12101]
  · have h := gap_lower (n := 12101) (a := (41710736421441 / 50000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334490561431 / 100000000000000 : ℝ))
      (E := (cell12101 ⟨19, by decide⟩).energy) (xi := (43932185357673 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12101 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12101]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12101])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12101) (a := (41710736421441 / 50000000000000 : ℝ)) (b := (85211021383 / 50000000000000 : ℝ)) (q := (2334490561431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12101])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12101]

theorem cert12102_0 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (16817097076663 / 20000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334251687981 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨0, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (16817097076663 / 20000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334251687981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_1 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (42025155864129 / 50000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334255654171 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨1, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (42025155864129 / 50000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334255654171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_2 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (84015163289213 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334259636637 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨2, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (84015163289213 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334259636637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_3 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83980040029053 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167131822727 / 50000000000000 : ℝ))
      (E := (cell12102 ⟨3, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83980040029053 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167131822727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_4 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83944941910849 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334267632593 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨4, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83944941910849 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334267632593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_5 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83909868897867 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334271607533 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨5, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83909868897867 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334271607533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_6 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (41937410476783 / 50000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167137789747 / 50000000000000 : ℝ))
      (E := (cell12102 ⟨6, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (41937410476783 / 50000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167137789747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_7 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (3274992111 / 3906250000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167139778717 / 50000000000000 : ℝ))
      (E := (cell12102 ⟨7, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (3274992111 / 3906250000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167139778717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_8 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83804800125813 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (466856710011 / 20000000000000 : ℝ))
      (E := (cell12102 ⟨8, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83804800125813 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (466856710011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_9 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83769827170241 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (11671437829 / 500000000000 : ℝ))
      (E := (cell12102 ⟨9, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83769827170241 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (11671437829 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_10 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (20933719784777 / 25000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (7294661109 / 312500000000 : ℝ))
      (E := (cell12102 ⟨10, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (20933719784777 / 25000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (7294661109 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_11 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (3347998239873 / 4000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (58357388129 / 2500000000000 : ℝ))
      (E := (cell12102 ⟨11, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (3347998239873 / 4000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (58357388129 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_12 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (8366505770799 / 10000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334299484253 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨12, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (8366505770799 / 10000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334299484253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_13 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83630184237389 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (583575874391 / 25000000000000 : ℝ))
      (E := (cell12102 ⟨13, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83630184237389 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (583575874391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_14 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83595335549989 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334307456129 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨14, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83595335549989 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334307456129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_15 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (41780255805471 / 50000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334311482927 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨15, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (41780255805471 / 50000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334311482927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_16 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83525712385581 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (5835788671 / 250000000000 : ℝ))
      (E := (cell12102 ⟨16, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83525712385581 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (5835788671 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_17 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83490937839419 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167159709421 / 50000000000000 : ℝ))
      (E := (cell12102 ⟨17, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83490937839419 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (1167159709421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_18 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83456187938151 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334323456629 / 100000000000000 : ℝ))
      (E := (cell12102 ⟨18, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83456187938151 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (2334323456629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12102_19 : CellCertificate 12102 (904189618266033 / 10000000000000000 : ℝ) (173564451792197 / 100000000000000000 : ℝ) (70285542324467 / 2000000000000000 : ℝ)
    (cell12102 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · norm_num [cell12102]
  · have h := gap_lower (n := 12102) (a := (83421462647647 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (145895463321 / 6250000000000 : ℝ))
      (E := (cell12102 ⟨19, by decide⟩).energy) (xi := (70285542324467 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12102 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12102]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12102])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12102) (a := (83421462647647 / 100000000000000 : ℝ)) (b := (85203891823 / 50000000000000 : ℝ)) (q := (145895463321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12102])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12102]

theorem cert12103_0 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (84085468721181 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (746908367 / 32000000000 : ℝ))
      (E := (cell12103 ⟨0, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (84085468721181 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (746908367 / 32000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_1 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (21012573852737 / 25000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (466818530313 / 20000000000000 : ℝ))
      (E := (cell12103 ⟨1, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (21012573852737 / 25000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (466818530313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_2 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (21003786829059 / 25000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334096615599 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨2, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (21003786829059 / 25000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334096615599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_3 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83980024399921 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (291762575849 / 12500000000000 : ℝ))
      (E := (cell12103 ⟨3, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83980024399921 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (291762575849 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_4 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (5246557914067 / 6250000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (14588153607 / 625000000000 : ℝ))
      (E := (cell12103 ⟨4, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (5246557914067 / 6250000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (14588153607 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_5 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83909853954959 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334108593917 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨5, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83909853954959 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334108593917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_6 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83874806353041 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (145882034419 / 6250000000000 : ℝ))
      (E := (cell12103 ⟨6, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83874806353041 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (145882034419 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_7 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83839783782973 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334116572183 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨7, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83839783782973 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334116572183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_8 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (419023931043 / 500000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (466824110253 / 20000000000000 : ℝ))
      (E := (cell12103 ⟨8, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (419023931043 / 500000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (466824110253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_9 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83769813593959 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (1167062277137 / 50000000000000 : ℝ))
      (E := (cell12103 ⟨9, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83769813593959 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (1167062277137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_10 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (3349394636131 / 4000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334128531423 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨10, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (3349394636131 / 4000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334128531423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_11 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (523124644381 / 625000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334132490573 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨11, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (523124644381 / 625000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334132490573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_12 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (16733009030323 / 20000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334136497361 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨12, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (16733009030323 / 20000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334136497361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_13 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (10453771502503 / 12500000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (1167070250583 / 50000000000000 : ℝ))
      (E := (cell12103 ⟨13, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (10453771502503 / 12500000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (1167070250583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_14 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (20898830917789 / 25000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (93365778041 / 4000000000000 : ℝ))
      (E := (cell12103 ⟨14, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (20898830917789 / 25000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (93365778041 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_15 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (16712100014033 / 20000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (466829693983 / 20000000000000 : ℝ))
      (E := (cell12103 ⟨15, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (16712100014033 / 20000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (466829693983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_16 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83525701182383 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (1167076224139 / 50000000000000 : ℝ))
      (E := (cell12103 ⟨16, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83525701182383 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (1167076224139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_17 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (41745463486663 / 50000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334156450547 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨17, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (41745463486663 / 50000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334156450547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_18 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83456177408689 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (72942513271 / 3125000000000 : ℝ))
      (E := (cell12103 ⟨18, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83456177408689 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (72942513271 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12103_19 : CellCertificate 12103 (904158966051459 / 10000000000000000 : ℝ) (1735501062305657 / 1000000000000000000 : ℝ) (175698972793257 / 5000000000000000 : ℝ)
    (cell12103 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · norm_num [cell12103]
  · have h := gap_lower (n := 12103) (a := (83421452454343 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334164434643 / 100000000000000 : ℝ))
      (E := (cell12103 ⟨19, by decide⟩).energy) (xi := (175698972793257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12103 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12103]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12103])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12103) (a := (83421452454343 / 100000000000000 : ℝ)) (b := (21299190869 / 12500000000000 : ℝ)) (q := (2334164434643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12103])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12103]

theorem cert12104_0 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (21021363015451 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (466785154677 / 20000000000000 : ℝ))
      (E := (cell12104 ⟨0, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (21021363015451 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (466785154677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_1 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (84050279096351 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333929758923 / 100000000000000 : ℝ))
      (E := (cell12104 ⟨1, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (84050279096351 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333929758923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_2 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (84015131345929 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333933762407 / 100000000000000 : ℝ))
      (E := (cell12104 ⟨2, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (84015131345929 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333933762407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_3 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (83980008773413 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (72935554253 / 3125000000000 : ℝ))
      (E := (cell12104 ⟨3, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (83980008773413 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (72935554253 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_4 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (83944911341877 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (93357667589 / 4000000000000 : ℝ))
      (E := (cell12104 ⟨4, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (83944911341877 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (93357667589 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_5 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (20977459753647 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166972845317 / 50000000000000 : ℝ))
      (E := (cell12104 ⟨5, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (20977459753647 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166972845317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_6 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (8387479175501 / 10000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333949690223 / 100000000000000 : ℝ))
      (E := (cell12104 ⟨6, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (8387479175501 / 10000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333949690223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_7 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (20959942381699 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (46679073949 / 2000000000000 : ℝ))
      (E := (cell12104 ⟨7, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (20959942381699 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (46679073949 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_8 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (41902386146897 / 50000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (583489415771 / 25000000000000 : ℝ))
      (E := (cell12104 ⟨8, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (41902386146897 / 50000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (583489415771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_9 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (2094245000501 / 2500000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333961653451 / 100000000000000 : ℝ))
      (E := (cell12104 ⟨9, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (2094245000501 / 2500000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333961653451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_10 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (41867426334881 / 50000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166982809379 / 50000000000000 : ℝ))
      (E := (cell12104 ⟨10, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (41867426334881 / 50000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166982809379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_11 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (20924982551843 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333969624873 / 100000000000000 : ℝ))
      (E := (cell12104 ⟨11, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (20924982551843 / 25000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333969624873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_12 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (2614532268671 / 3125000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333973621447 / 100000000000000 : ℝ))
      (E := (cell12104 ⟨12, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (2614532268671 / 3125000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (2333973621447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_13 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (5226884987803 / 6250000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166988807919 / 50000000000000 : ℝ))
      (E := (cell12104 ⟨13, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (5226884987803 / 6250000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166988807919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_14 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (83595311794469 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166990807577 / 50000000000000 : ℝ))
      (E := (cell12104 ⟨14, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (83595311794469 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166990807577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_15 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (8356048853149 / 10000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (466797113631 / 20000000000000 : ℝ))
      (E := (cell12104 ⟨15, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (8356048853149 / 10000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (466797113631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_16 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (16705137996249 / 20000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166994769749 / 50000000000000 : ℝ))
      (E := (cell12104 ⟨16, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (16705137996249 / 20000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166994769749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_17 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (333963664437 / 400000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (291749191943 / 12500000000000 : ℝ))
      (E := (cell12104 ⟨17, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (333963664437 / 400000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (291749191943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_18 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (83456166881201 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166998781203 / 50000000000000 : ℝ))
      (E := (cell12104 ⟨18, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (83456166881201 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (1166998781203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12104_19 : CellCertificate 12104 (904128318723361 / 10000000000000000 : ℝ) (433839407600339 / 250000000000000000 : ℝ) (351368184752343 / 10000000000000000 : ℝ)
    (cell12104 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · norm_num [cell12104]
  · have h := gap_lower (n := 12104) (a := (83421442262971 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (291750188697 / 12500000000000 : ℝ))
      (E := (cell12104 ⟨19, by decide⟩).energy) (xi := (351368184752343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12104 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12104]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12104])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12104) (a := (83421442262971 / 100000000000000 : ℝ)) (b := (170379272681 / 100000000000000 : ℝ)) (q := (291750188697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12104])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12104]

theorem cert12105_0 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (84085435405183 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (291720376221 / 12500000000000 : ℝ))
      (E := (cell12105 ⟨0, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (84085435405183 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (291720376221 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_1 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (42025131392233 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333766976247 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨1, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (42025131392233 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333766976247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_2 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (84015115378289 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583442740371 / 25000000000000 : ℝ))
      (E := (cell12105 ⟨2, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (84015115378289 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583442740371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_3 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83979993149529 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333774975549 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨3, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83979993149529 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333774975549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_4 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (41972448030631 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333778970411 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨4, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (41972448030631 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333778970411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_5 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (41954912038377 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333782955547 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨5, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (41954912038377 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333782955547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_6 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83874777159471 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333786940169 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨6, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83874777159471 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333786940169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_7 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (20959938818267 / 25000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583447733309 / 25000000000000 : ℝ))
      (E := (cell12105 ⟨7, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (20959938818267 / 25000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583447733309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_8 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83804758381393 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166897442757 / 50000000000000 : ℝ))
      (E := (cell12105 ⟨8, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83804758381393 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166897442757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_9 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83769786448483 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583449730321 / 25000000000000 : ℝ))
      (E := (cell12105 ⟨9, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83769786448483 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583449730321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_10 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83734839438567 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333802874867 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨10, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83734839438567 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333802874867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_11 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (4184995865803 / 5000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333806870057 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨11, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (4184995865803 / 5000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333806870057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_12 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (41832510022781 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333810856509 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨12, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (41832510022781 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333810856509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_13 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83630147591861 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166907420789 / 50000000000000 : ℝ))
      (E := (cell12105 ⟨13, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83630147591861 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166907420789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_14 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (10449412489991 / 12500000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333818832371 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨14, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (10449412489991 / 12500000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333818832371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_15 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (41780238497459 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166911417871 / 50000000000000 : ℝ))
      (E := (cell12105 ⟨15, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (41780238497459 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166911417871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_16 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (41762839391083 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (116691340009 / 5000000000000 : ℝ))
      (E := (cell12105 ⟨16, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (41762839391083 / 50000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (116691340009 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_17 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83490905247191 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583457697529 / 25000000000000 : ℝ))
      (E := (cell12105 ⟨17, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83490905247191 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (583457697529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_18 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83456156355687 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166917405833 / 50000000000000 : ℝ))
      (E := (cell12105 ⟨18, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83456156355687 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (1166917405833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12105_19 : CellCertificate 12105 (452048838140259 / 5000000000000000 : ℝ) (1735214222203187 / 1000000000000000000 : ℝ) (87834607279561 / 2500000000000000 : ℝ)
    (cell12105 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · norm_num [cell12105]
  · have h := gap_lower (n := 12105) (a := (83421432073529 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333838754317 / 100000000000000 : ℝ))
      (E := (cell12105 ⟨19, by decide⟩).energy) (xi := (87834607279561 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12105 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12105]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12105])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12105) (a := (83421432073529 / 100000000000000 : ℝ)) (b := (85182510417 / 50000000000000 : ℝ)) (q := (2333838754317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12105])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12105]

theorem cert12106_0 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (42042709375659 / 50000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333600413771 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨0, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (42042709375659 / 50000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333600413771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_1 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (21012561618823 / 25000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333604361307 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨1, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (21012561618823 / 25000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333604361307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_2 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (21003774853329 / 25000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333608386203 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨2, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (21003774853329 / 25000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333608386203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_3 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (8397997752827 / 10000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (466722465031 / 20000000000000 : ℝ))
      (E := (cell12106 ⟨3, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (8397997752827 / 10000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (466722465031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_4 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (41972440391613 / 50000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166808180671 / 50000000000000 : ℝ))
      (E := (cell12106 ⟨4, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (41972440391613 / 50000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166808180671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_5 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83909809141457 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (466724066159 / 20000000000000 : ℝ))
      (E := (cell12106 ⟨5, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83909809141457 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (466724066159 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_6 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (3354990502657 / 4000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2278929981 / 97656250000 : ℝ))
      (E := (cell12106 ⟨6, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (3354990502657 / 4000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2278929981 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_7 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83839741021789 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166814139771 / 50000000000000 : ℝ))
      (E := (cell12106 ⟨7, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83839741021789 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166814139771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_8 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83804744471397 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (291704034561 / 12500000000000 : ℝ))
      (E := (cell12106 ⟨8, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83804744471397 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (291704034561 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_9 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (10471221609911 / 12500000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166818149911 / 50000000000000 : ℝ))
      (E := (cell12106 ⟨9, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (10471221609911 / 12500000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166818149911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_10 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83734826209691 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333640241771 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨10, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83734826209691 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333640241771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_11 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83699904427021 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (233364422613 / 10000000000000 : ℝ))
      (E := (cell12106 ⟨11, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83699904427021 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (233364422613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_12 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (41832503747941 / 50000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333648260577 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨12, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (41832503747941 / 50000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333648260577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_13 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83630135381061 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333652236439 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨13, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83630135381061 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333652236439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_14 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83595288047531 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333656218823 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨14, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83595288047531 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333656218823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_15 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83560465460447 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (291707526823 / 12500000000000 : ℝ))
      (E := (cell12106 ⟨15, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83560465460447 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (291707526823 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_16 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83525667585147 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333664172207 / 100000000000000 : ℝ))
      (E := (cell12106 ⟨16, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83525667585147 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (2333664172207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_17 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83490894387147 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166834078063 / 50000000000000 : ℝ))
      (E := (cell12106 ⟨17, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83490894387147 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166834078063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_18 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (16691229166429 / 20000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166836086227 / 50000000000000 : ℝ))
      (E := (cell12106 ⟨18, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (16691229166429 / 20000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166836086227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12106_19 : CellCertificate 12106 (180813407744341 / 2000000000000000 : ℝ) (1735070837705273 / 1000000000000000000 : ℝ) (175654339341321 / 5000000000000000 : ℝ)
    (cell12106 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · norm_num [cell12106]
  · have h := gap_lower (n := 12106) (a := (83421421886017 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166838084433 / 50000000000000 : ℝ))
      (E := (cell12106 ⟨19, by decide⟩).energy) (xi := (175654339341321 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12106 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12106]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12106])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12106) (a := (83421421886017 / 100000000000000 : ℝ)) (b := (17035077141 / 10000000000000 : ℝ)) (q := (1166838084433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12106])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12106]

theorem cert12107_0 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (84085402100207 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333437927653 / 100000000000000 : ℝ))
      (E := (cell12107 ⟨0, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (84085402100207 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333437927653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_1 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (84050230168829 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (466688382821 / 20000000000000 : ℝ))
      (E := (cell12107 ⟨1, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (84050230168829 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (466688382821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_2 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (84015083451011 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166722931597 / 50000000000000 : ℝ))
      (E := (cell12107 ⟨2, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (84015083451011 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166722931597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_3 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (83979961909633 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (233344984273 / 10000000000000 : ℝ))
      (E := (cell12107 ⟨3, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (83979961909633 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (233344984273 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_4 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (8394486550777 / 10000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (58336346563 / 2500000000000 : ℝ))
      (E := (cell12107 ⟨4, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (8394486550777 / 10000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (58336346563 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_5 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (41954897104347 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (36460278381 / 1562500000000 : ℝ))
      (E := (cell12107 ⟨5, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (41954897104347 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (36460278381 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_6 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (8387474797587 / 10000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (583365457309 / 25000000000000 : ℝ))
      (E := (cell12107 ⟨6, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (8387474797587 / 10000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (583365457309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_7 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (41919863386479 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (58336644857 / 2500000000000 : ℝ))
      (E := (cell12107 ⟨7, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (41919863386479 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (58336644857 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_8 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (16760946112761 / 20000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166734889039 / 50000000000000 : ℝ))
      (E := (cell12107 ⟨8, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (16760946112761 / 20000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166734889039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_9 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (41884879656227 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166736894533 / 50000000000000 : ℝ))
      (E := (cell12107 ⟨9, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (41884879656227 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166736894533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_10 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (20933703245783 / 25000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333477777453 / 100000000000000 : ℝ))
      (E := (cell12107 ⟨10, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (20933703245783 / 25000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333477777453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_11 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (83699891540257 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (291685218887 / 12500000000000 : ℝ))
      (E := (cell12107 ⟨11, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (83699891540257 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (291685218887 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_12 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (41832497474217 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166742887813 / 50000000000000 : ℝ))
      (E := (cell12107 ⟨12, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (41832497474217 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166742887813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_13 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (1672602463449 / 2000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (583372435593 / 25000000000000 : ℝ))
      (E := (cell12107 ⟨13, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (1672602463449 / 2000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (583372435593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_14 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (83595276177279 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (58337342911 / 2500000000000 : ℝ))
      (E := (cell12107 ⟨14, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (83595276177279 / 100000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (58337342911 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_15 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (41780226964039 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333497704681 / 100000000000000 : ℝ))
      (E := (cell12107 ⟨15, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (41780226964039 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333497704681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_16 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (16705131278037 / 20000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166750856851 / 50000000000000 : ℝ))
      (E := (cell12107 ⟨16, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (16705131278037 / 20000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166750856851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_17 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (41745441764559 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333505691719 / 100000000000000 : ℝ))
      (E := (cell12107 ⟨17, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (41745441764559 / 50000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333505691719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_18 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (5216008456911 / 6250000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166754851469 / 50000000000000 : ℝ))
      (E := (cell12107 ⟨18, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (5216008456911 / 6250000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (1166754851469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12107_19 : CellCertificate 12107 (9040364060457 / 100000000000000 : ℝ) (1734927476901741 / 1000000000000000000 : ℝ) (351278933443959 / 10000000000000000 : ℝ)
    (cell12107 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · norm_num [cell12107]
  · have h := gap_lower (n := 12107) (a := (16684282340087 / 20000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333513695037 / 100000000000000 : ℝ))
      (E := (cell12107 ⟨19, by decide⟩).energy) (xi := (351278933443959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12107 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12107]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12107])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12107) (a := (16684282340087 / 20000000000000 : ℝ)) (b := (21292065551 / 12500000000000 : ℝ)) (q := (2333513695037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12107])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12107]

theorem cert12108_0 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (84085385451851 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (466655110283 / 20000000000000 : ℝ))
      (E := (cell12108 ⟨0, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (84085385451851 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (466655110283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_1 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (21012553466269 / 25000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333279519109 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨1, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (21012553466269 / 25000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333279519109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_2 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (21003766872843 / 25000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (58332087701 / 2500000000000 : ℝ))
      (E := (cell12108 ⟨2, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (21003766872843 / 25000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (58332087701 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_3 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (41989973146809 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333287470463 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨3, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (41989973146809 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333287470463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_4 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (20986212558723 / 25000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333291473947 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨4, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (20986212558723 / 25000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333291473947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_5 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (41954889639233 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (72915483443 / 3125000000000 : ℝ))
      (E := (cell12108 ⟨5, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (41954889639233 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (72915483443 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_6 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (83874733387807 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333299468359 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨6, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (83874733387807 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333299468359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_7 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (41919856263287 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333303477451 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨7, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (41919856263287 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333303477451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_8 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (83804716658617 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (291663431027 / 12500000000000 : ℝ))
      (E := (cell12108 ⟨8, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (83804716658617 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (291663431027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_9 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (83769745747979 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (36457991359 / 1562500000000 : ℝ))
      (E := (cell12108 ⟨9, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (83769745747979 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (36457991359 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_10 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (8373479975889 / 10000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (466663084787 / 20000000000000 : ℝ))
      (E := (cell12108 ⟨10, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (8373479975889 / 10000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (466663084787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_11 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (83699878655767 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333319386953 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨11, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (83699878655767 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333319386953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_12 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (16732996480643 / 20000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (116666170083 / 5000000000000 : ℝ))
      (E := (cell12108 ⟨12, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (16732996480643 / 20000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (116666170083 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_13 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (3345204438641 / 4000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (1166663679691 / 50000000000000 : ℝ))
      (E := (cell12108 ⟨13, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (3345204438641 / 4000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (1166663679691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_14 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (83595264309171 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2278643929 / 97656250000 : ℝ))
      (E := (cell12108 ⟨14, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (83595264309171 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2278643929 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_15 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (8356044239781 / 10000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333335364133 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨15, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (8356044239781 / 10000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333335364133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_16 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (83525645197281 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333339366547 / 100000000000000 : ℝ))
      (E := (cell12108 ⟨16, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (83525645197281 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (2333339366547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_17 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (5218179542069 / 6250000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (9114622417 / 390625000000 : ℝ))
      (E := (cell12108 ⟨17, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (5218179542069 / 6250000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (9114622417 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_18 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (83456124790979 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (1166673672477 / 50000000000000 : ℝ))
      (E := (cell12108 ⟨18, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (83456124790979 / 100000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (1166673672477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

theorem cert12108_19 : CellCertificate 12108 (904005778251281 / 10000000000000000 : ℝ) (1734784139786717 / 1000000000000000000 : ℝ) (175624596700311 / 5000000000000000 : ℝ)
    (cell12108 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · norm_num [cell12108]
  · have h := gap_lower (n := 12108) (a := (41710700758391 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (233335133283 / 10000000000000 : ℝ))
      (E := (cell12108 ⟨19, by decide⟩).energy) (xi := (175624596700311 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12108 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12108]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12108])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12108) (a := (41710700758391 / 50000000000000 : ℝ)) (b := (42580569957 / 25000000000000 : ℝ)) (q := (233335133283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12108])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12108]

end BstLean.Part281
