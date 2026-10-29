import BstLean.Part253CutoffObstruction

namespace BstLean.Part253

noncomputable def certifiedNumerator (i : Fin 60) : ℝ :=
  BstLean.Part254.capTable i + centreTable (centreGroup i)

end BstLean.Part253
