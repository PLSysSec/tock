import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferVecQueuePushCorrect
open Classical

namespace F

theorem slice_set (s : Slc Int) (h1 : i.toNat < l.toNat ∨ i.toNat > r.toNat) (h2 : l.toNat <= r.toNat)
  : collections_sslice_subslice (collections_sslice_set s i e) l r = collections_sslice_subslice s l r := by
    grind [List.drop_set, List.take_set_of_le]

theorem add_one_sub (h : l <= r) : r + 1 - l = (r - l) + 1 := by omega

theorem slice_set_push (s : Slc Int) (h1 : r < s.length) (h2 : l.toNat ≤ r)
  : collections_sslice_subslice (collections_sslice_set s r e) l (r + 1) = collections_sslice_subslice s l r ++ [e] := by
    simp [collections_sslice_subslice, collections_sslice_set]
    rw [add_one_sub]
    rw [List.take_add_one]
    simp_all
    grind [List.drop_set, List.take_set_of_le]
    assumption

theorem slice00 (s : Slc Int)
  : collections_sslice_subslice s 0 0 = [] := by grind

def CollectionsRingBufferVecQueuePushCorrect_proof : CollectionsRingBufferVecQueuePushCorrect := by
  unfold CollectionsRingBufferVecQueuePushCorrect
  intro rb vq elem c1 c2 _ _ _ success
  intro nrb _ _ _ seq _ ifs
  and_intros
  · intro h ; rcases h with ⟨sh, hdgttl⟩
    have := ifs sh ; rcases this  with ⟨⟨nrbhdeq, nrbtleq⟩, nrbringeq⟩
    by_cases h : rb.hd > rb.tl
    · have := c1 h
      rw [←this]
      unfold collections_sslice_append collections_sslice_push
      have : collections_sslice_subslice nrb.ring nrb.hd (collections_sslice_len nrb.ring) = collections_sslice_subslice rb.ring rb.hd (collections_sslice_len rb.ring) := by
        grind [slice_set]
      rw [List.append_assoc, this, List.append_cancel_left_eq]
      have : nrb.tl = rb.tl + 1 := by
        grind [←Int.emod_eq_of_lt]
      rw [this, nrbringeq]
      grind [slice_set_push]
    · by_cases h' : rb.tl = collections_sslice_len rb.ring - 1
      · have : nrb.tl = 0 := by
          rw [nrbtleq, h'] ; simp
        rw [this]
        simp at h
        have := c2 h
        have foo : collections_sslice_len rb.ring = collections_sslice_len nrb.ring := by grind
        rw [←this, slice00, collections_sslice_append, collections_sslice_push, List.append_nil]
        rw [←foo, nrbringeq]
        conv => lhs ; arg 3 ; rw [←Int.sub_add_cancel (collections_sslice_len rb.ring) 1]
        rw [←h']
        grind [slice_set_push]
      · have : nrb.tl = rb.tl + 1 := by
          rw [nrbtleq]
          apply Int.emod_eq_of_lt
          omega
          omega
        grind
  · intro h ; rcases h with ⟨sh, hdgttl⟩
    have := ifs sh ; rcases this  with ⟨⟨nrbhdeq, nrbtleq⟩, nrbringeq⟩
    by_cases h : rb.hd > rb.tl
    · have := c1 h
      by_cases rb.tl = collections_sslice_len rb.ring - 1
      · grind
      · rw [← this]
        have : nrb.tl = rb.tl + 1 := by grind [←Int.emod_eq_of_lt]
        rw [this, nrbhdeq, nrbringeq]
        grind
    · simp at h
      have := c2 h
      rw [← this, nrbhdeq]
      by_cases rb.tl = collections_sslice_len rb.ring - 1
      · simp_all ; grind
      · have : nrb.tl = rb.tl + 1 := by
          simp_all ; grind [←Int.emod_eq_of_lt]
        rw [this, nrbringeq, collections_sslice_push]
        grind [slice_set_push]

end F
