import BstLean.Part281Frame12100
import BstLean.Part280Rows12100
import BstLean.Part281RowBridge
import BstLean.Part281Odd
namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188
open BstLean.Part192 BstLean.Part196 BstLean.Part280

theorem energyCap12100 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (scalarRow12100.table i).energy ≤ m2Caps.Ecap := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨2,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨3,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨4,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨5,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨6,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨7,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨8,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨9,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨10,h⟩ =>
      first
      | change (21911045058783 / 31250000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (21911045058783 / 31250000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (21911045058783 / 31250000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨11,h⟩ =>
      first
      | change (3502843476273641 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3502843476273641 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3502843476273641 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨12,h⟩ =>
      first
      | change (3499923042261229 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3499923042261229 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3499923042261229 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨13,h⟩ =>
      first
      | change (6994011803641153 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6994011803641153 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6994011803641153 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨14,h⟩ =>
      first
      | change (1747046024713189 / 2500000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (1747046024713189 / 2500000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (1747046024713189 / 2500000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨15,h⟩ =>
      first
      | change (6982362959150711 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6982362959150711 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6982362959150711 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨16,h⟩ =>
      first
      | change (6976548373572227 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6976548373572227 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6976548373572227 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨17,h⟩ =>
      first
      | change (6970740331198013 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6970740331198013 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6970740331198013 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨18,h⟩ =>
      first
      | change (6964938821151997 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6964938821151997 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6964938821151997 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨19,h⟩ =>
      first
      | change (6959143832601061 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6959143832601061 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6959143832601061 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨20,h⟩ =>
      first
      | change (6953355354754769 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6953355354754769 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6953355354754769 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨21,h⟩ =>
      first
      | change (6947573376865103 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6947573376865103 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6947573376865103 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨22,h⟩ =>
      first
      | change (6941797888226199 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6941797888226199 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6941797888226199 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨23,h⟩ =>
      first
      | change (1387205775634817 / 2000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (1387205775634817 / 2000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (1387205775634817 / 2000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨24,h⟩ =>
      first
      | change (277210653443457 / 400000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (277210653443457 / 400000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (277210653443457 / 400000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨25,h⟩ =>
      first
      | change (6924510251382257 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6924510251382257 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6924510251382257 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨26,h⟩ =>
      first
      | change (6918760613521743 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6918760613521743 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6918760613521743 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨27,h⟩ =>
      first
      | change (1728254353001479 / 2500000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (1728254353001479 / 2500000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (1728254353001479 / 2500000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨28,h⟩ =>
      first
      | change (6907280636376429 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6907280636376429 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6907280636376429 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨29,h⟩ =>
      first
      | change (1725387569053827 / 2500000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (1725387569053827 / 2500000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (1725387569053827 / 2500000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨30,h⟩ =>
      first
      | change (6895826321144703 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6895826321144703 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6895826321144703 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨31,h⟩ =>
      first
      | change (6890108760826651 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6890108760826651 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6890108760826651 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨32,h⟩ =>
      first
      | change (1721099396240707 / 2500000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (1721099396240707 / 2500000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (1721099396240707 / 2500000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨33,h⟩ =>
      first
      | change (6878692783294313 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6878692783294313 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6878692783294313 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨34,h⟩ =>
      first
      | change (6872994345601349 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6872994345601349 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6872994345601349 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨35,h⟩ =>
      first
      | change (686730226170311 / 1000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (686730226170311 / 1000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (686730226170311 / 1000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨36,h⟩ =>
      first
      | change (6861616521457463 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6861616521457463 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6861616521457463 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨37,h⟩ =>
      first
      | change (6855937114760743 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6855937114760743 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6855937114760743 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨38,h⟩ =>
      first
      | change (3425132015773759 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3425132015773759 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3425132015773759 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨39,h⟩ =>
      first
      | change (6844597261790363 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6844597261790363 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6844597261790363 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨40,h⟩ =>
      first
      | change (6838936795499637 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6838936795499637 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6838936795499637 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨41,h⟩ =>
      first
      | change (854160327840407 / 1250000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (854160327840407 / 1250000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (854160327840407 / 1250000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨42,h⟩ =>
      first
      | change (6827634733546473 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6827634733546473 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6827634733546473 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨43,h⟩ =>
      first
      | change (3410996559045829 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3410996559045829 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3410996559045829 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨44,h⟩ =>
      first
      | change (3408178883259039 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3408178883259039 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3408178883259039 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨45,h⟩ =>
      first
      | change (6810728669021683 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6810728669021683 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6810728669021683 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨46,h⟩ =>
      first
      | change (1701276453958723 / 2500000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (1701276453958723 / 2500000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (1701276453958723 / 2500000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨47,h⟩ =>
      first
      | change (3399744598613189 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3399744598613189 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3399744598613189 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨48,h⟩ =>
      first
      | change (6793878803500857 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6793878803500857 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6793878803500857 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨49,h⟩ =>
      first
      | change (6788274624998881 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6788274624998881 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6788274624998881 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨50,h⟩ =>
      first
      | change (6782676652096631 / 10000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (6782676652096631 / 10000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (6782676652096631 / 10000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨51,h⟩ =>
      first
      | change (3388542437602853 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3388542437602853 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3388542437602853 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨52,h⟩ =>
      first
      | change (3385749642386463 / 5000000000000000 : ℝ) ≤ (0.702 : ℝ)
        exact_mod_cast (show (3385749642386463 / 5000000000000000 : ℚ) ≤ (0.702 : ℚ) from by decide)
      | change (3385749642386463 / 5000000000000000 : ℝ) ≤ m2Caps.Ecap
        norm_num [m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)


noncomputable def localRoot12100 : SharpLocalSupply 12100 m2Caps (sharpTableN 12100)
    (m2Guard 12100) (BstLean.Part159.Hof WorldRow12100.worldPackage.hidden) :=
  localRoot_from_numerics (by norm_num) (by norm_num) WorldRow12100.worldPackage rfl
    WorldRow12100.product_lower (WorldRow12100.producthi.2.trans (by norm_num))
    scalarRow12100 (fun _ hi => N12100.sourceNumerics12100 hi)
    (by norm_num [scalarRow12100,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow12100,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow12100,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    energyCap12100

theorem compatible12100 : agent12100.charge ≤ master12100.retainedCharge := by
  rw [show master12100.retainedCharge = scalar12100.retainedCharge from
    congrArg (fun C => C.retainedCharge) preserves12100]
  norm_num [agent12100,scalar12100]

noncomputable def row12100 : BstLean.Part259.RowInputs 12100 :=
  row_from_sharp (by norm_num) (by norm_num) N12100.frameData12100 agent12100 master12100
    BstLean.Part280.m2Certificate12100 localRoot12100 (by norm_num [BstLean.Part280.Sharp.Row12100.rootTarget,agent12100])
    rfl rfl (by norm_num [agent12100]) compatible12100

theorem classifier_stated_12100 (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 12100).prod (sampMeas (10^12) 12100)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12100) t
        BstLean.Part156.aL (10^12) x.1 x.2)} :=
  classifier_from_sharp_row row12100 (fun _ hc => hc.1) t
end BstLean.Part281
