import BstLean.Part264Data0
import BstLean.Part264Data1
import BstLean.Part264Data2
import BstLean.Part264Data3
import BstLean.Part264Data4

/-! Finite scalar coverage includes every integer in the requested interval. -/
namespace BstLean.Part264
open Set BstLean.Part263

theorem repair_coverage (n : ℕ) (hn : n ∈ Icc 12225 12349) :
    ∃ R : ScalarRow n, Nonempty (FrameRepair n R) := by
  obtain ⟨hl, hu⟩ := hn
  interval_cases n
  · exact ⟨scalarRow12225, ⟨repair12225⟩⟩
  · exact ⟨scalarRow12226, ⟨repair12226⟩⟩
  · exact ⟨scalarRow12227, ⟨repair12227⟩⟩
  · exact ⟨scalarRow12228, ⟨repair12228⟩⟩
  · exact ⟨scalarRow12229, ⟨repair12229⟩⟩
  · exact ⟨scalarRow12230, ⟨repair12230⟩⟩
  · exact ⟨scalarRow12231, ⟨repair12231⟩⟩
  · exact ⟨scalarRow12232, ⟨repair12232⟩⟩
  · exact ⟨scalarRow12233, ⟨repair12233⟩⟩
  · exact ⟨scalarRow12234, ⟨repair12234⟩⟩
  · exact ⟨scalarRow12235, ⟨repair12235⟩⟩
  · exact ⟨scalarRow12236, ⟨repair12236⟩⟩
  · exact ⟨scalarRow12237, ⟨repair12237⟩⟩
  · exact ⟨scalarRow12238, ⟨repair12238⟩⟩
  · exact ⟨scalarRow12239, ⟨repair12239⟩⟩
  · exact ⟨scalarRow12240, ⟨repair12240⟩⟩
  · exact ⟨scalarRow12241, ⟨repair12241⟩⟩
  · exact ⟨scalarRow12242, ⟨repair12242⟩⟩
  · exact ⟨scalarRow12243, ⟨repair12243⟩⟩
  · exact ⟨scalarRow12244, ⟨repair12244⟩⟩
  · exact ⟨scalarRow12245, ⟨repair12245⟩⟩
  · exact ⟨scalarRow12246, ⟨repair12246⟩⟩
  · exact ⟨scalarRow12247, ⟨repair12247⟩⟩
  · exact ⟨scalarRow12248, ⟨repair12248⟩⟩
  · exact ⟨scalarRow12249, ⟨repair12249⟩⟩
  · exact ⟨scalarRow12250, ⟨repair12250⟩⟩
  · exact ⟨scalarRow12251, ⟨repair12251⟩⟩
  · exact ⟨scalarRow12252, ⟨repair12252⟩⟩
  · exact ⟨scalarRow12253, ⟨repair12253⟩⟩
  · exact ⟨scalarRow12254, ⟨repair12254⟩⟩
  · exact ⟨scalarRow12255, ⟨repair12255⟩⟩
  · exact ⟨scalarRow12256, ⟨repair12256⟩⟩
  · exact ⟨scalarRow12257, ⟨repair12257⟩⟩
  · exact ⟨scalarRow12258, ⟨repair12258⟩⟩
  · exact ⟨scalarRow12259, ⟨repair12259⟩⟩
  · exact ⟨scalarRow12260, ⟨repair12260⟩⟩
  · exact ⟨scalarRow12261, ⟨repair12261⟩⟩
  · exact ⟨scalarRow12262, ⟨repair12262⟩⟩
  · exact ⟨scalarRow12263, ⟨repair12263⟩⟩
  · exact ⟨scalarRow12264, ⟨repair12264⟩⟩
  · exact ⟨scalarRow12265, ⟨repair12265⟩⟩
  · exact ⟨scalarRow12266, ⟨repair12266⟩⟩
  · exact ⟨scalarRow12267, ⟨repair12267⟩⟩
  · exact ⟨scalarRow12268, ⟨repair12268⟩⟩
  · exact ⟨scalarRow12269, ⟨repair12269⟩⟩
  · exact ⟨scalarRow12270, ⟨repair12270⟩⟩
  · exact ⟨scalarRow12271, ⟨repair12271⟩⟩
  · exact ⟨scalarRow12272, ⟨repair12272⟩⟩
  · exact ⟨scalarRow12273, ⟨repair12273⟩⟩
  · exact ⟨scalarRow12274, ⟨repair12274⟩⟩
  · exact ⟨scalarRow12275, ⟨repair12275⟩⟩
  · exact ⟨scalarRow12276, ⟨repair12276⟩⟩
  · exact ⟨scalarRow12277, ⟨repair12277⟩⟩
  · exact ⟨scalarRow12278, ⟨repair12278⟩⟩
  · exact ⟨scalarRow12279, ⟨repair12279⟩⟩
  · exact ⟨scalarRow12280, ⟨repair12280⟩⟩
  · exact ⟨scalarRow12281, ⟨repair12281⟩⟩
  · exact ⟨scalarRow12282, ⟨repair12282⟩⟩
  · exact ⟨scalarRow12283, ⟨repair12283⟩⟩
  · exact ⟨scalarRow12284, ⟨repair12284⟩⟩
  · exact ⟨scalarRow12285, ⟨repair12285⟩⟩
  · exact ⟨scalarRow12286, ⟨repair12286⟩⟩
  · exact ⟨scalarRow12287, ⟨repair12287⟩⟩
  · exact ⟨scalarRow12288, ⟨repair12288⟩⟩
  · exact ⟨scalarRow12289, ⟨repair12289⟩⟩
  · exact ⟨scalarRow12290, ⟨repair12290⟩⟩
  · exact ⟨scalarRow12291, ⟨repair12291⟩⟩
  · exact ⟨scalarRow12292, ⟨repair12292⟩⟩
  · exact ⟨scalarRow12293, ⟨repair12293⟩⟩
  · exact ⟨scalarRow12294, ⟨repair12294⟩⟩
  · exact ⟨scalarRow12295, ⟨repair12295⟩⟩
  · exact ⟨scalarRow12296, ⟨repair12296⟩⟩
  · exact ⟨scalarRow12297, ⟨repair12297⟩⟩
  · exact ⟨scalarRow12298, ⟨repair12298⟩⟩
  · exact ⟨scalarRow12299, ⟨repair12299⟩⟩
  · exact ⟨scalarRow12300, ⟨repair12300⟩⟩
  · exact ⟨scalarRow12301, ⟨repair12301⟩⟩
  · exact ⟨scalarRow12302, ⟨repair12302⟩⟩
  · exact ⟨scalarRow12303, ⟨repair12303⟩⟩
  · exact ⟨scalarRow12304, ⟨repair12304⟩⟩
  · exact ⟨scalarRow12305, ⟨repair12305⟩⟩
  · exact ⟨scalarRow12306, ⟨repair12306⟩⟩
  · exact ⟨scalarRow12307, ⟨repair12307⟩⟩
  · exact ⟨scalarRow12308, ⟨repair12308⟩⟩
  · exact ⟨scalarRow12309, ⟨repair12309⟩⟩
  · exact ⟨scalarRow12310, ⟨repair12310⟩⟩
  · exact ⟨scalarRow12311, ⟨repair12311⟩⟩
  · exact ⟨scalarRow12312, ⟨repair12312⟩⟩
  · exact ⟨scalarRow12313, ⟨repair12313⟩⟩
  · exact ⟨scalarRow12314, ⟨repair12314⟩⟩
  · exact ⟨scalarRow12315, ⟨repair12315⟩⟩
  · exact ⟨scalarRow12316, ⟨repair12316⟩⟩
  · exact ⟨scalarRow12317, ⟨repair12317⟩⟩
  · exact ⟨scalarRow12318, ⟨repair12318⟩⟩
  · exact ⟨scalarRow12319, ⟨repair12319⟩⟩
  · exact ⟨scalarRow12320, ⟨repair12320⟩⟩
  · exact ⟨scalarRow12321, ⟨repair12321⟩⟩
  · exact ⟨scalarRow12322, ⟨repair12322⟩⟩
  · exact ⟨scalarRow12323, ⟨repair12323⟩⟩
  · exact ⟨scalarRow12324, ⟨repair12324⟩⟩
  · exact ⟨scalarRow12325, ⟨repair12325⟩⟩
  · exact ⟨scalarRow12326, ⟨repair12326⟩⟩
  · exact ⟨scalarRow12327, ⟨repair12327⟩⟩
  · exact ⟨scalarRow12328, ⟨repair12328⟩⟩
  · exact ⟨scalarRow12329, ⟨repair12329⟩⟩
  · exact ⟨scalarRow12330, ⟨repair12330⟩⟩
  · exact ⟨scalarRow12331, ⟨repair12331⟩⟩
  · exact ⟨scalarRow12332, ⟨repair12332⟩⟩
  · exact ⟨scalarRow12333, ⟨repair12333⟩⟩
  · exact ⟨scalarRow12334, ⟨repair12334⟩⟩
  · exact ⟨scalarRow12335, ⟨repair12335⟩⟩
  · exact ⟨scalarRow12336, ⟨repair12336⟩⟩
  · exact ⟨scalarRow12337, ⟨repair12337⟩⟩
  · exact ⟨scalarRow12338, ⟨repair12338⟩⟩
  · exact ⟨scalarRow12339, ⟨repair12339⟩⟩
  · exact ⟨scalarRow12340, ⟨repair12340⟩⟩
  · exact ⟨scalarRow12341, ⟨repair12341⟩⟩
  · exact ⟨scalarRow12342, ⟨repair12342⟩⟩
  · exact ⟨scalarRow12343, ⟨repair12343⟩⟩
  · exact ⟨scalarRow12344, ⟨repair12344⟩⟩
  · exact ⟨scalarRow12345, ⟨repair12345⟩⟩
  · exact ⟨scalarRow12346, ⟨repair12346⟩⟩
  · exact ⟨scalarRow12347, ⟨repair12347⟩⟩
  · exact ⟨scalarRow12348, ⟨repair12348⟩⟩
  · exact ⟨scalarRow12349, ⟨repair12349⟩⟩

end BstLean.Part264
