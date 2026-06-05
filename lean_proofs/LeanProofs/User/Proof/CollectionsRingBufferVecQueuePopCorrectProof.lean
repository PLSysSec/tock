import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CollectionsRingBufferVecQueuePopCorrect
open Classical

namespace F

theorem pop_front_subslice (s : Slc Int) (h : l < r) (hl : 0 ≤ l) :
    collections_sslice_pop_front (collections_sslice_subslice s l r) =
    collections_sslice_subslice s (l + 1) r := by
  simp only [collections_sslice_pop_front, collections_sslice_subslice]
  rw [List.drop_take, List.drop_drop]
  have h1 : l.toNat + 1 = (l + 1).toNat := by omega
  have h2 : r.toNat - l.toNat - 1 = r.toNat - (l + 1).toNat := by omega
  rw [h1, h2]

theorem pop_front_append_subslice (s : Slc Int) (t : Slc Int)
    (hl : 0 ≤ l) (hlt : l + 1 ≤ r) (hr : r.toNat ≤ s.length) :
    collections_sslice_pop_front (collections_sslice_append
      (collections_sslice_subslice s l r) t) =
    collections_sslice_append (collections_sslice_subslice s (l + 1) r) t := by
  simp only [collections_sslice_pop_front, collections_sslice_append, collections_sslice_subslice]
  rw [List.drop_append_of_le_length]
  · rw [List.drop_take, List.drop_drop]
    have h1 : l.toNat + 1 = (l + 1).toNat := by omega
    have h2 : r.toNat - l.toNat - 1 = r.toNat - (l + 1).toNat := by omega
    rw [h1, h2]
  · simp [List.length_take, Nat.min_def]
    split <;> omega

theorem pop_front_singleton_append (s : Slc Int) (t : Slc Int)
    (hl : 0 ≤ l) (hend : l + 1 = r) (hr : r.toNat ≤ s.length) :
    collections_sslice_pop_front (collections_sslice_append
      (collections_sslice_subslice s l r) t) = t := by
  simp only [collections_sslice_pop_front, collections_sslice_append, collections_sslice_subslice]
  rw [List.drop_append_of_le_length]
  · rw [List.drop_take, List.drop_drop]
    have h0 : r.toNat - l.toNat - 1 = 0 := by omega
    simp [h0]
  · simp [List.length_take, Nat.min_def]
    split <;> omega

def CollectionsRingBufferVecQueuePopCorrect_proof : CollectionsRingBufferVecQueuePopCorrect := by
  unfold CollectionsRingBufferVecQueuePopCorrect
  intro rb vq c1 c2 hdne _ htl_bounds hhd_bounds hringlen res
  intro nrb _ _ _ hres_eq htl_eq hring_eq ifs ifns
  and_intros
  · intro hdgttl
    rcases Classical.em res with hrt | hrf
    · have hnewhd := ifs hrt
      by_cases hcase : rb.hd > rb.tl
      · have hvq := c1 hcase
        by_cases hnotlast : rb.hd + 1 < collections_sslice_len rb.ring
        · have hnewhd_eq : nrb.hd = rb.hd + 1 := by
            rw [hnewhd]
            apply Int.emod_eq_of_lt <;> grind
          rw [hring_eq, htl_eq, hnewhd_eq, ←hvq]
          grind [pop_front_append_subslice, collections_sslice_len]
        · exfalso
          have heq : rb.hd + 1 = collections_sslice_len rb.ring := by
            have := hhd_bounds.2; omega
          have hmod0 : nrb.hd = 0 := by rw [hnewhd, heq, Int.emod_self]
          grind
      · simp at hcase
        have hlt : rb.hd < rb.tl := by grind
        have hnewhd_eq : nrb.hd = rb.hd + 1 := by
          rw [hnewhd]
          apply Int.emod_eq_of_lt <;> grind
        grind
    · exact absurd hdne (hres_eq ▸ hrf)
  · intro hdletl
    rcases Classical.em res with hrt | hrf
    · have hnewhd := ifs hrt
      by_cases hcase : rb.hd > rb.tl
      · have hvq := c1 hcase
        by_cases hwrap : rb.hd = collections_sslice_len rb.ring - 1
        · have hnewhd0 : nrb.hd = 0 := by
            rw [hnewhd, hwrap]
            have hrlen : collections_sslice_len rb.ring - 1 + 1 = collections_sslice_len rb.ring := by
              have := hringlen; omega
            rw [hrlen, Int.emod_self]
          rw [hring_eq, htl_eq, hnewhd0, ←hvq]
          grind [pop_front_singleton_append]
        · have hnotlast : rb.hd + 1 < collections_sslice_len rb.ring := by
            have := hhd_bounds.2; omega
          have hnewhd_eq : nrb.hd = rb.hd + 1 := by
            rw [hnewhd]
            apply Int.emod_eq_of_lt <;> grind
          grind
      · simp at hcase
        have hlt : rb.hd < rb.tl := by grind
        have hvq := c2 (Int.le_of_lt hlt)
        have hnewhd_eq : nrb.hd = rb.hd + 1 := by
          rw [hnewhd]
          apply Int.emod_eq_of_lt <;> grind
        rw [hring_eq, htl_eq, hnewhd_eq, ←hvq]
        symm
        exact pop_front_subslice rb.ring hlt hhd_bounds.1
    · exact absurd hdne (hres_eq ▸ hrf)

end F
