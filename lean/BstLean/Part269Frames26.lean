import BstLean.Part269Frames26Step0
import BstLean.Part269Frames26Step1
import BstLean.Part269Frames26Step2
import BstLean.Part269Frames26Step3
import BstLean.Part269Frames26Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard26 (n : ℕ) (hn : n ∈ Icc 13000 13024) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13000.frameData13000
  · exact N13001.frameData13001
  · exact N13002.frameData13002
  · exact N13003.frameData13003
  · exact N13004.frameData13004
  · exact N13005.frameData13005
  · exact N13006.frameData13006
  · exact N13007.frameData13007
  · exact N13008.frameData13008
  · exact N13009.frameData13009
  · exact N13010.frameData13010
  · exact N13011.frameData13011
  · exact N13012.frameData13012
  · exact N13013.frameData13013
  · exact N13014.frameData13014
  · exact N13015.frameData13015
  · exact N13016.frameData13016
  · exact N13017.frameData13017
  · exact N13018.frameData13018
  · exact N13019.frameData13019
  · exact N13020.frameData13020
  · exact N13021.frameData13021
  · exact N13022.frameData13022
  · exact N13023.frameData13023
  · exact N13024.frameData13024
end BstLean.Part269
