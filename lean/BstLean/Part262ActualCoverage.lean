import BstLean.Part262ActualData0
import BstLean.Part262ActualData1
import BstLean.Part262ActualData2
import BstLean.Part262ActualShard3Step6
import BstLean.Part262ActualData4
import BstLean.Part262FrameRoot
import BstLean.Part262Data0
import BstLean.Part262Data1
import BstLean.Part262Data2
import BstLean.Part262Data3
import BstLean.Part262Data4

namespace BstLean.Part262
open Real Set

theorem actual_root_coverage : ∀ n ∈ Icc (12225 : ℕ) 12349,
    ∃ a : BstLean.Part192.AgentParameters, Nonempty (ActualRootCertificate n a.root) ∧
      (1499145 / 10 ^ 9 : ℝ) + 3 / 10000 ≤ a.charge := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := hn
  interval_cases n
  · exact ⟨BstLean.Part259.agent12225, ⟨actualCertificate12225⟩, allocation12225⟩
  · exact ⟨BstLean.Part259.agent12226, ⟨actualCertificate12226⟩, allocation12226⟩
  · exact ⟨BstLean.Part259.agent12227, ⟨actualCertificate12227⟩, allocation12227⟩
  · exact ⟨BstLean.Part259.agent12228, ⟨actualCertificate12228⟩, allocation12228⟩
  · exact ⟨BstLean.Part259.agent12229, ⟨actualCertificate12229⟩, allocation12229⟩
  · exact ⟨BstLean.Part259.agent12230, ⟨actualCertificate12230⟩, allocation12230⟩
  · exact ⟨BstLean.Part259.agent12231, ⟨actualCertificate12231⟩, allocation12231⟩
  · exact ⟨BstLean.Part259.agent12232, ⟨actualCertificate12232⟩, allocation12232⟩
  · exact ⟨BstLean.Part259.agent12233, ⟨actualCertificate12233⟩, allocation12233⟩
  · exact ⟨BstLean.Part259.agent12234, ⟨actualCertificate12234⟩, allocation12234⟩
  · exact ⟨BstLean.Part259.agent12235, ⟨actualCertificate12235⟩, allocation12235⟩
  · exact ⟨BstLean.Part259.agent12236, ⟨actualCertificate12236⟩, allocation12236⟩
  · exact ⟨BstLean.Part259.agent12237, ⟨actualCertificate12237⟩, allocation12237⟩
  · exact ⟨BstLean.Part259.agent12238, ⟨actualCertificate12238⟩, allocation12238⟩
  · exact ⟨BstLean.Part259.agent12239, ⟨actualCertificate12239⟩, allocation12239⟩
  · exact ⟨BstLean.Part259.agent12240, ⟨actualCertificate12240⟩, allocation12240⟩
  · exact ⟨BstLean.Part259.agent12241, ⟨actualCertificate12241⟩, allocation12241⟩
  · exact ⟨BstLean.Part259.agent12242, ⟨actualCertificate12242⟩, allocation12242⟩
  · exact ⟨BstLean.Part259.agent12243, ⟨actualCertificate12243⟩, allocation12243⟩
  · exact ⟨BstLean.Part259.agent12244, ⟨actualCertificate12244⟩, allocation12244⟩
  · exact ⟨BstLean.Part259.agent12245, ⟨actualCertificate12245⟩, allocation12245⟩
  · exact ⟨BstLean.Part259.agent12246, ⟨actualCertificate12246⟩, allocation12246⟩
  · exact ⟨BstLean.Part259.agent12247, ⟨actualCertificate12247⟩, allocation12247⟩
  · exact ⟨BstLean.Part259.agent12248, ⟨actualCertificate12248⟩, allocation12248⟩
  · exact ⟨BstLean.Part259.agent12249, ⟨actualCertificate12249⟩, allocation12249⟩
  · exact ⟨BstLean.Part259.agent12250, ⟨actualCertificate12250⟩, allocation12250⟩
  · exact ⟨BstLean.Part259.agent12251, ⟨actualCertificate12251⟩, allocation12251⟩
  · exact ⟨BstLean.Part259.agent12252, ⟨actualCertificate12252⟩, allocation12252⟩
  · exact ⟨BstLean.Part259.agent12253, ⟨actualCertificate12253⟩, allocation12253⟩
  · exact ⟨BstLean.Part259.agent12254, ⟨actualCertificate12254⟩, allocation12254⟩
  · exact ⟨BstLean.Part259.agent12255, ⟨actualCertificate12255⟩, allocation12255⟩
  · exact ⟨BstLean.Part259.agent12256, ⟨actualCertificate12256⟩, allocation12256⟩
  · exact ⟨BstLean.Part259.agent12257, ⟨actualCertificate12257⟩, allocation12257⟩
  · exact ⟨BstLean.Part259.agent12258, ⟨actualCertificate12258⟩, allocation12258⟩
  · exact ⟨BstLean.Part259.agent12259, ⟨actualCertificate12259⟩, allocation12259⟩
  · exact ⟨BstLean.Part259.agent12260, ⟨actualCertificate12260⟩, allocation12260⟩
  · exact ⟨BstLean.Part259.agent12261, ⟨actualCertificate12261⟩, allocation12261⟩
  · exact ⟨BstLean.Part259.agent12262, ⟨actualCertificate12262⟩, allocation12262⟩
  · exact ⟨BstLean.Part259.agent12263, ⟨actualCertificate12263⟩, allocation12263⟩
  · exact ⟨BstLean.Part259.agent12264, ⟨actualCertificate12264⟩, allocation12264⟩
  · exact ⟨BstLean.Part259.agent12265, ⟨actualCertificate12265⟩, allocation12265⟩
  · exact ⟨BstLean.Part259.agent12266, ⟨actualCertificate12266⟩, allocation12266⟩
  · exact ⟨BstLean.Part259.agent12267, ⟨actualCertificate12267⟩, allocation12267⟩
  · exact ⟨BstLean.Part259.agent12268, ⟨actualCertificate12268⟩, allocation12268⟩
  · exact ⟨BstLean.Part259.agent12269, ⟨actualCertificate12269⟩, allocation12269⟩
  · exact ⟨BstLean.Part259.agent12270, ⟨actualCertificate12270⟩, allocation12270⟩
  · exact ⟨BstLean.Part259.agent12271, ⟨actualCertificate12271⟩, allocation12271⟩
  · exact ⟨BstLean.Part259.agent12272, ⟨actualCertificate12272⟩, allocation12272⟩
  · exact ⟨BstLean.Part259.agent12273, ⟨actualCertificate12273⟩, allocation12273⟩
  · exact ⟨BstLean.Part259.agent12274, ⟨actualCertificate12274⟩, allocation12274⟩
  · exact ⟨BstLean.Part259.agent12275, ⟨actualCertificate12275⟩, allocation12275⟩
  · exact ⟨BstLean.Part259.agent12276, ⟨actualCertificate12276⟩, allocation12276⟩
  · exact ⟨BstLean.Part259.agent12277, ⟨actualCertificate12277⟩, allocation12277⟩
  · exact ⟨BstLean.Part259.agent12278, ⟨actualCertificate12278⟩, allocation12278⟩
  · exact ⟨BstLean.Part259.agent12279, ⟨actualCertificate12279⟩, allocation12279⟩
  · exact ⟨BstLean.Part259.agent12280, ⟨actualCertificate12280⟩, allocation12280⟩
  · exact ⟨BstLean.Part259.agent12281, ⟨actualCertificate12281⟩, allocation12281⟩
  · exact ⟨BstLean.Part259.agent12282, ⟨actualCertificate12282⟩, allocation12282⟩
  · exact ⟨BstLean.Part259.agent12283, ⟨actualCertificate12283⟩, allocation12283⟩
  · exact ⟨BstLean.Part259.agent12284, ⟨actualCertificate12284⟩, allocation12284⟩
  · exact ⟨BstLean.Part259.agent12285, ⟨actualCertificate12285⟩, allocation12285⟩
  · exact ⟨BstLean.Part259.agent12286, ⟨actualCertificate12286⟩, allocation12286⟩
  · exact ⟨BstLean.Part259.agent12287, ⟨actualCertificate12287⟩, allocation12287⟩
  · exact ⟨BstLean.Part259.agent12288, ⟨actualCertificate12288⟩, allocation12288⟩
  · exact ⟨BstLean.Part259.agent12289, ⟨actualCertificate12289⟩, allocation12289⟩
  · exact ⟨BstLean.Part259.agent12290, ⟨actualCertificate12290⟩, allocation12290⟩
  · exact ⟨BstLean.Part259.agent12291, ⟨actualCertificate12291⟩, allocation12291⟩
  · exact ⟨BstLean.Part259.agent12292, ⟨actualCertificate12292⟩, allocation12292⟩
  · exact ⟨BstLean.Part259.agent12293, ⟨actualCertificate12293⟩, allocation12293⟩
  · exact ⟨BstLean.Part259.agent12294, ⟨actualCertificate12294⟩, allocation12294⟩
  · exact ⟨BstLean.Part259.agent12295, ⟨actualCertificate12295⟩, allocation12295⟩
  · exact ⟨BstLean.Part259.agent12296, ⟨actualCertificate12296⟩, allocation12296⟩
  · exact ⟨BstLean.Part259.agent12297, ⟨actualCertificate12297⟩, allocation12297⟩
  · exact ⟨BstLean.Part259.agent12298, ⟨actualCertificate12298⟩, allocation12298⟩
  · exact ⟨BstLean.Part259.agent12299, ⟨actualCertificate12299⟩, allocation12299⟩
  · exact ⟨BstLean.Part259.agent12300, ⟨actualCertificate12300⟩, allocation12300⟩
  · exact ⟨BstLean.Part259.agent12301, ⟨actualCertificate12301⟩, allocation12301⟩
  · exact ⟨BstLean.Part259.agent12302, ⟨actualCertificate12302⟩, allocation12302⟩
  · exact ⟨BstLean.Part259.agent12303, ⟨actualCertificate12303⟩, allocation12303⟩
  · exact ⟨BstLean.Part259.agent12304, ⟨actualCertificate12304⟩, allocation12304⟩
  · exact ⟨BstLean.Part259.agent12305, ⟨actualCertificate12305⟩, allocation12305⟩
  · exact ⟨BstLean.Part259.agent12306, ⟨actualCertificate12306⟩, allocation12306⟩
  · exact ⟨BstLean.Part259.agent12307, ⟨actualCertificate12307⟩, allocation12307⟩
  · exact ⟨BstLean.Part259.agent12308, ⟨actualCertificate12308⟩, allocation12308⟩
  · exact ⟨BstLean.Part259.agent12309, ⟨actualCertificate12309⟩, allocation12309⟩
  · exact ⟨BstLean.Part259.agent12310, ⟨actualCertificate12310⟩, allocation12310⟩
  · exact ⟨BstLean.Part259.agent12311, ⟨actualCertificate12311⟩, allocation12311⟩
  · exact ⟨BstLean.Part259.agent12312, ⟨actualCertificate12312⟩, allocation12312⟩
  · exact ⟨BstLean.Part259.agent12313, ⟨actualCertificate12313⟩, allocation12313⟩
  · exact ⟨BstLean.Part259.agent12314, ⟨actualCertificate12314⟩, allocation12314⟩
  · exact ⟨BstLean.Part259.agent12315, ⟨actualCertificate12315⟩, allocation12315⟩
  · exact ⟨BstLean.Part259.agent12316, ⟨actualCertificate12316⟩, allocation12316⟩
  · exact ⟨BstLean.Part259.agent12317, ⟨actualCertificate12317⟩, allocation12317⟩
  · exact ⟨BstLean.Part259.agent12318, ⟨actualCertificate12318⟩, allocation12318⟩
  · exact ⟨BstLean.Part259.agent12319, ⟨actualCertificate12319⟩, allocation12319⟩
  · exact ⟨BstLean.Part259.agent12320, ⟨actualCertificate12320⟩, allocation12320⟩
  · exact ⟨BstLean.Part259.agent12321, ⟨actualCertificate12321⟩, allocation12321⟩
  · exact ⟨BstLean.Part259.agent12322, ⟨actualCertificate12322⟩, allocation12322⟩
  · exact ⟨BstLean.Part259.agent12323, ⟨actualCertificate12323⟩, allocation12323⟩
  · exact ⟨BstLean.Part259.agent12324, ⟨actualCertificate12324⟩, allocation12324⟩
  · exact ⟨BstLean.Part259.agent12325, ⟨actualCertificate12325⟩, allocation12325⟩
  · exact ⟨BstLean.Part259.agent12326, ⟨actualCertificate12326⟩, allocation12326⟩
  · exact ⟨BstLean.Part259.agent12327, ⟨actualCertificate12327⟩, allocation12327⟩
  · exact ⟨BstLean.Part259.agent12328, ⟨actualCertificate12328⟩, allocation12328⟩
  · exact ⟨BstLean.Part259.agent12329, ⟨actualCertificate12329⟩, allocation12329⟩
  · exact ⟨BstLean.Part259.agent12330, ⟨actualCertificate12330⟩, allocation12330⟩
  · exact ⟨BstLean.Part259.agent12331, ⟨actualCertificate12331⟩, allocation12331⟩
  · exact ⟨BstLean.Part259.agent12332, ⟨actualCertificate12332⟩, allocation12332⟩
  · exact ⟨BstLean.Part259.agent12333, ⟨actualCertificate12333⟩, allocation12333⟩
  · exact ⟨BstLean.Part259.agent12334, ⟨actualCertificate12334⟩, allocation12334⟩
  · exact ⟨BstLean.Part259.agent12335, ⟨actualCertificate12335⟩, allocation12335⟩
  · exact ⟨BstLean.Part259.agent12336, ⟨actualCertificate12336⟩, allocation12336⟩
  · exact ⟨BstLean.Part259.agent12337, ⟨actualCertificate12337⟩, allocation12337⟩
  · exact ⟨BstLean.Part259.agent12338, ⟨actualCertificate12338⟩, allocation12338⟩
  · exact ⟨BstLean.Part259.agent12339, ⟨actualCertificate12339⟩, allocation12339⟩
  · exact ⟨BstLean.Part259.agent12340, ⟨actualCertificate12340⟩, allocation12340⟩
  · exact ⟨BstLean.Part259.agent12341, ⟨actualCertificate12341⟩, allocation12341⟩
  · exact ⟨BstLean.Part259.agent12342, ⟨actualCertificate12342⟩, allocation12342⟩
  · exact ⟨BstLean.Part259.agent12343, ⟨actualCertificate12343⟩, allocation12343⟩
  · exact ⟨BstLean.Part259.agent12344, ⟨actualCertificate12344⟩, allocation12344⟩
  · exact ⟨BstLean.Part259.agent12345, ⟨actualCertificate12345⟩, allocation12345⟩
  · exact ⟨BstLean.Part259.agent12346, ⟨actualCertificate12346⟩, allocation12346⟩
  · exact ⟨BstLean.Part259.agent12347, ⟨actualCertificate12347⟩, allocation12347⟩
  · exact ⟨BstLean.Part259.agent12348, ⟨actualCertificate12348⟩, allocation12348⟩
  · exact ⟨BstLean.Part259.agent12349, ⟨actualCertificate12349⟩, allocation12349⟩

theorem actual_base_root_coverage : ∀ n ∈ Icc (12225 : ℕ) 12349,
    ∃ a : BstLean.Part192.AgentParameters,
      (1499145 / 10 ^ 9 : ℝ) + 3 / 10000 ≤ a.charge ∧
      ∀ H : Set (BstLean.Part157.Ret n), LocalRootSupply n H →
        Nonempty (BaseRootSupply n H a.root (1499145 / 10 ^ 9)) := by
  intro n hn
  obtain ⟨a, ⟨C⟩, ha⟩ := actual_root_coverage n hn
  exact ⟨a, ha, fun H L => ⟨actualBaseRootSupply C H L⟩⟩

end BstLean.Part262
