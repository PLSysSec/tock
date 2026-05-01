import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__1__RemoveFirstMatching
open Classical

namespace F

open CollectionsRingBufferImpl1RemoveFirstMatchingKVarSolutions

def k0 : Int → Slc Int → Int → Int → Int → Prop :=
  fun idx ring _ _ _ =>
    0 ≤ idx ∧ idx < collections_sslice_len ring

def k3 : Int → Int → Slc Int → Slc Int → Int → Int → Int → Int → Int → Prop → Int → Int → Prop :=
  fun next_slot slot ring ringo heado _ _ _ _ _ _ _ =>
    0 ≤ next_slot ∧ next_slot < collections_sslice_len ringo ∧
    collections_sslice_len ring > 1 ∧
    heado < collections_sslice_len ring ∧
    slot < collections_sslice_len ring ∧
    0 ≤ slot ∧
    next_slot < collections_sslice_len ring ∧
    collections_sslice_len ring = collections_sslice_len ringo



def k4 :  Int → Int → Int → Slc Int → Slc Int → Int → Int → Int → Int → Int → Prop → Int → Int → Prop :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    True

theorem len_set (s : Slc Int)
  : collections_sslice_len (collections_sslice_set s p v) = collections_sslice_len s := by
  grind

set_option maxHeartbeats 400000
def CollectionsRingBufferImpl__1__RemoveFirstMatching_proof : CollectionsRingBufferImpl__1__RemoveFirstMatching := by
  unfold CollectionsRingBufferImpl__1__RemoveFirstMatching
  exists k0 ; exists k1 ; exists k2 ; exists k3
  exists k4 ; exists k5 ; exists k6 ; exists k7
  repeat (any_goals
    first
      | (intro)
      | apply And.intro
      | rw [len_set]
      | grind only
  )
  any_goals (grind only [k0, k1, k2, k3, k4, k5, k6, k7])
  any_goals (simp_all [k3])
  any_goals (apply Int.emod_nonneg ; omega)
  any_goals (apply Int.emod_lt_of_pos ; omega)
end F
