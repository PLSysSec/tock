import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferImpl__Retain
open Classical

namespace F

open CollectionsRingBufferImplRetainKVarSolutions

def k6 (_a'₃₅ : Int) (_a'₃₆ : Int) (_a'₃₇ : (Slc Int)) (_a'₃₈ : (Slc Int)) (_a'₃₉ : Int) (_a'₄₀ : Int) (_a'₄₁ : Int) (_a'₄₂ : Int) (_a'₄₃ : Int) (_a'₄₄ : Int) (_a'₄₅ : (Slc Int)) (_a'₄₆ : Int) (_a'₄₇ : Prop) (_a'₄₈ : Int) : Prop :=
  True
def k8 (_a'₄₉ : Int) (_a'₅₀ : (Slc Int)) (_a'₅₁ : (Slc Int)) (_a'₅₂ : Int) (_a'₅₃ : Int) (_a'₅₄ : Int) (_a'₅₅ : Int) (_a'₅₆ : Int) (_a'₅₇ : Int) (_a'₅₈ : (Slc Int)) (_a'₅₉ : Int) (_a'₆₀ : Prop) (_a'₆₁ : Int) : Prop :=
  True
def k0 (dst : Int) (_a'₆₃ : Int) (src : Int) (ring : (Slc Int)) (ringo : (Slc Int)) (_a'₆₇ : Int) (_a'₆₈ : Int) (_a'₆₉ : Int) : Prop :=
  (dst ≥ 0) ∧ dst < collections_sslice_len ring ∧ collections_sslice_len ring > 1 ∧
  collections_sslice_len ring = collections_sslice_len ringo ∧
  src < collections_sslice_len ring
def k1 (_a'₇₀ : Int) (_a'₇₁ : Int) (_a'₇₂ : Int) (_a'₇₃ : Int) (_ring : (Slc Int)) (_ringo : (Slc Int)) (_a'₇₆ : Int) (_a'₇₇ : Int) (_a'₇₈ : Int) : Prop :=
  True

theorem len_set2 (s : Slc Int)
  : collections_sslice_len (collections_sslice_set s p v) = collections_sslice_len s := by
  grind

def CollectionsRingBufferImpl__Retain_proof : CollectionsRingBufferImpl__Retain := by
  unfold CollectionsRingBufferImpl__Retain
  exists k0 ; exists k1 ; exists k2 ; exists k3 ; exists k4 ; exists k5
  exists k6 ; exists k7 ; exists k8 ; exists k9 ; exists k10
  repeat (any_goals
    first
      | (intro)
      | apply And.intro
      | grind [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10]
  )
  · unfold k0 k5 at *
    rename_i h _ _ _ _ _
    rcases h with h | ⟨⟨_, _, mod, _⟩,_⟩
    grind
    rw [mod] ; apply Int.emod_nonneg ; omega
  · unfold k0 k5 at *
    rename_i h _ _ _ _ _
    rcases h with h | ⟨⟨_, dseq, mod, _⟩, ⟨_, ⟨⟨⟨_, _, set⟩, _⟩, _⟩⟩⟩
    · grind
    · simp_all [len_set2]
      apply Int.emod_lt_of_pos ; omega
    · simp_all
      rw [dseq]
      apply Int.emod_lt_of_pos
      all_goals grind only [k3]
  · unfold k0 k5 at *
    rename_i h _ _ _ _ _
    rcases h with h | ⟨⟨_, _, mod, _⟩, ⟨_, ⟨⟨⟨_, _, set⟩, _⟩, _⟩⟩⟩
    · simp_all
      apply Int.emod_lt_of_pos ; omega
    · rw [set, len_set2]
      simp_all
      apply Int.emod_lt_of_pos ; omega
    · simp_all
      apply Int.emod_lt_of_pos ; grind only [k3]
end F
