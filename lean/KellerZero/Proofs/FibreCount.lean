import KellerZero.Open

/-!
# O6: the fibre has as many points as the cubic has simple roots

The map `(x, y, z) ↦ u w` sends the fibre over a target with `c ≠ 0` to the simple roots of its
cubic (`cubic_eq_zero`, `cubicDeriv_eq`), is injective there (`eq_of_same_root`) and reaches
every simple root (`point_of_simple_root`).
-/

theorem KellerZero.Proofs.FibreCount : KellerZero.Open.FibreCount := by
  intro a b c hc
  refine Set.ncard_congr
    (fun p _ => (1 + p.1 * p.2.1) * (5 - 3 * (1 + p.1 * p.2.1) - p.1 ^ 2 * p.2.2)) ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ ⟨hP, hQ, hR⟩
    simp only at hP hQ hR ⊢
    refine ⟨?_, ?_⟩
    · have h := KellerZero.cubic_eq_zero x y z
      rwa [hP, hQ, hR] at h
    · have h := KellerZero.cubicDeriv_eq x y z
      rw [hQ, hR] at h
      rw [h]
      have hc' := hc
      rw [← hR, KellerZero.R_eq_mul] at hc'
      exact mul_ne_zero two_ne_zero (right_ne_zero_of_mul hc')
  · rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ ⟨-, hQ, hR⟩ ⟨-, hQ', hR'⟩ hm
    simp only at hQ hR hQ' hR' hm
    obtain ⟨rfl, rfl, rfl⟩ := KellerZero.eq_of_same_root (hQ.trans hQ'.symm) (hR.trans hR'.symm)
      (by rw [hR]; exact hc) hm
    rfl
  · rintro m ⟨hm, hd⟩
    obtain ⟨x, y, z, hP, hQ, hR, hxyz⟩ := KellerZero.point_of_simple_root a b c m hc hm hd
    exact ⟨(x, y, z), ⟨hP, hQ, hR⟩, hxyz⟩
