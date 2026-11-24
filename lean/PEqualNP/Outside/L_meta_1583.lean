import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1583

lemma mod_add_one_inj {m a b : ℕ} (ha : a < m) (hb : b < m)
    (h : (a + 1) % m = (b + 1) % m) : a = b := by
  by_cases ha1 : a + 1 < m
  · by_cases hb1 : b + 1 < m
    · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at h
      omega
    · have hb2 : b + 1 = m := by omega
      rw [Nat.mod_eq_of_lt ha1, hb2, Nat.mod_self] at h
      omega
  · have ha2 : a + 1 = m := by omega
    by_cases hb1 : b + 1 < m
    · rw [ha2, Nat.mod_self, Nat.mod_eq_of_lt hb1] at h
      omega
    · omega

lemma exists_cycle {N m : ℕ} (T0 : Finset (Fin N)) (hm : 3 ≤ m) (hcard : T0.card = m) :
    ∃ sigma : Fin N → Fin N,
      (∀ x ∈ T0, sigma x ∈ T0) ∧
      Set.InjOn sigma ↑T0 ∧
      (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) := by
  classical
  have hm0 : 0 < m := by omega
  let e : {x // x ∈ T0} ≃ Fin m := T0.equivFinOfCardEq hcard
  let step : Fin m → Fin m := fun i => ⟨(i.val + 1) % m, Nat.mod_lt _ hm0⟩
  let sigma : Fin N → Fin N := fun x =>
    if hx : x ∈ T0 then (e.symm (step (e ⟨x, hx⟩))).val else x
  have hmem : ∀ x ∈ T0, sigma x ∈ T0 := by
    intro x hx
    simp only [sigma, dif_pos hx]
    exact (e.symm (step (e ⟨x, hx⟩))).property
  have hinj : Set.InjOn sigma ↑T0 := by
    intro x hx y hy hxy
    have hx' : x ∈ T0 := Finset.mem_coe.mp hx
    have hy' : y ∈ T0 := Finset.mem_coe.mp hy
    simp only [sigma, dif_pos hx', dif_pos hy'] at hxy
    have hsub : e.symm (step (e ⟨x, hx'⟩)) = e.symm (step (e ⟨y, hy'⟩)) := Subtype.ext hxy
    have hstep : step (e ⟨x, hx'⟩) = step (e ⟨y, hy'⟩) := e.symm.injective hsub
    have hval : ((e ⟨x, hx'⟩).val + 1) % m = ((e ⟨y, hy'⟩).val + 1) % m :=
      congrArg Fin.val hstep
    have heq : e ⟨x, hx'⟩ = e ⟨y, hy'⟩ :=
      Fin.ext (mod_add_one_inj (e ⟨x, hx'⟩).isLt (e ⟨y, hy'⟩).isLt hval)
    exact congrArg Subtype.val (e.injective heq)
  have hiter : ∀ (k : ℕ) (i : Fin m),
      sigma^[k] (e.symm i).val = (e.symm ⟨(i.val + k) % m, Nat.mod_lt _ hm0⟩).val := by
    intro k
    induction k with
    | zero =>
      intro i
      simp only [Function.iterate_zero_apply, Nat.add_zero]
      have hmod : (⟨i.val % m, Nat.mod_lt _ hm0⟩ : Fin m) = i :=
        Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [hmod]
    | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply', ih i]
      have hprop := (e.symm ⟨(i.val + k) % m, Nat.mod_lt _ hm0⟩).property
      simp only [sigma, dif_pos hprop, Subtype.coe_eta, Equiv.apply_symm_apply, step]
      have hmod : ((i.val + k) % m + 1) % m = (i.val + (k + 1)) % m := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
      congr 2
      exact Fin.ext hmod
  have htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y := by
    intro x hx y hy
    let i := e ⟨x, hx⟩
    let j := e ⟨y, hy⟩
    refine ⟨j.val + m - i.val, ?_⟩
    have hx_eq : x = (e.symm i).val := by simp [i]
    have hy_eq : y = (e.symm j).val := by simp [j]
    rw [hx_eq, hiter]
    have hmod : (i.val + (j.val + m - i.val)) % m = j.val := by
      have hi : i.val < m := i.isLt
      have h1 : i.val + (j.val + m - i.val) = j.val + m := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    have hfin : (⟨(i.val + (j.val + m - i.val)) % m, Nat.mod_lt _ hm0⟩ : Fin m) = j :=
      Fin.ext hmod
    rw [hfin, hy_eq]
  exact ⟨sigma, hmem, hinj, htrans⟩

lemma sigma_sigma_ne {N m : ℕ} {T0 : Finset (Fin N)} {sigma : Fin N → Fin N}
    (hm : 3 ≤ m) (hcard : T0.card = m)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    {x : Fin N} (hx : x ∈ T0) : sigma (sigma x) ≠ x := by
  intro h2
  have hiter : ∀ k : ℕ, sigma^[k] x = x ∨ sigma^[k] x = sigma x := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]; exact Or.inr rfl
      · rw [h, h2]; exact Or.inl rfl
  have hsub : T0 ⊆ ({x, sigma x} : Finset (Fin N)) := by
    intro y hy
    obtain ⟨k, rfl⟩ := htrans x hx y hy
    rcases hiter k with h | h <;> simp [h]
  have hle : T0.card ≤ ({x, sigma x} : Finset (Fin N)).card := Finset.card_le_card hsub
  have h2le : ({x, sigma x} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
  omega

lemma sigma_ne {N m : ℕ} {T0 : Finset (Fin N)} {sigma : Fin N → Fin N}
    (hm : 3 ≤ m) (hcard : T0.card = m)
    (htrans : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    {x : Fin N} (hx : x ∈ T0) : sigma x ≠ x := by
  intro h1
  exact sigma_sigma_ne hm hcard htrans hx (by rw [h1, h1])

lemma inter_eq_of_card_one {N : ℕ} {A B : Finset (Fin N)} (h : (A ∩ B).card = 1)
    {u v : Fin N} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B) : u = v := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h
  have hu : u ∈ A ∩ B := Finset.mem_inter.mpr ⟨huA, huB⟩
  have hv : v ∈ A ∩ B := Finset.mem_inter.mpr ⟨hvA, hvB⟩
  rw [hz, Finset.mem_singleton] at hu hv
  exact hu.trans hv.symm

lemma rotor_sub_T0 {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N}
    {T0 : Finset (Fin N)} {sigma : Fin N → Fin N} {x0 : Fin N}
    {B : Fin N → Fin N → Finset (Fin N)}
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hmem : ∀ x ∈ T0, sigma x ∈ T0) (hx0 : x0 ∈ T0)
    (hB1 : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s →
      B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x})
    (hB2 : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0})
    {s p : Fin N} (hs : s ≠ i0) (hp : p ∈ L s) : B s p ⊆ T0 := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hinter s i0 hs)
  have hzmem : z ∈ L s ∩ L i0 := by rw [hz]; exact Finset.mem_singleton_self z
  obtain ⟨hzs, hzi0⟩ := Finset.mem_inter.mp hzmem
  by_cases hzT : z ∈ T0
  · rw [hB1 s hs p hp z hzT hzs]
    split_ifs
    · exact Finset.empty_subset T0
    · exact Finset.singleton_subset_iff.mpr (hmem z hzT)
  · rw [hB2 s hs z (Finset.mem_sdiff.mpr ⟨hzi0, hzT⟩) hzs p hp]
    exact Finset.singleton_subset_iff.mpr hx0

lemma main :
    ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  intro q m N L i0 T0 _hmq_q hm _hmq _hN _hcard hinter _hcov hT0 hT0card
  refine ⟨exists_cycle T0 hm hT0card, ?_⟩
  intro sigma x0 B ⟨hmem, _hinj, htrans⟩ hx0 hB1 hB2
  constructor
  · intro s hs p hp
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hinter s i0 hs)
    have hzmem : z ∈ L s ∩ L i0 := by rw [hz]; exact Finset.mem_singleton_self z
    obtain ⟨hzs, hzi0⟩ := Finset.mem_inter.mp hzmem
    have hdisj : B s p ∩ L s = ∅ := by
      by_cases hzT : z ∈ T0
      · rw [hB1 s hs p hp z hzT hzs]
        split_ifs with hpz
        · simp
        · rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
          rw [Finset.mem_singleton] at hv1
          subst hv1
          have heq := inter_eq_of_card_one (hinter s i0 hs) hv2 (hT0 (hmem z hzT)) hzs hzi0
          exact sigma_ne hm hT0card htrans hzT heq
      · rw [hB2 s hs z (Finset.mem_sdiff.mpr ⟨hzi0, hzT⟩) hzs p hp]
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
        rw [Finset.mem_singleton] at hv1
        subst hv1
        have heq := inter_eq_of_card_one (hinter s i0 hs) hv2 (hT0 hx0) hzs hzi0
        exact hzT (heq ▸ hx0)
    refine ⟨hdisj, Or.inl ?_, ?_⟩
    · by_cases hzT : z ∈ T0
      · rw [hB1 s hs p hp z hzT hzs]
        by_cases hpz : p = z
        · refine ⟨p, hpz ▸ hzT, by simp⟩
        · refine ⟨sigma z, hmem z hzT, ?_⟩
          simp [hpz]
      · rw [hB2 s hs z (Finset.mem_sdiff.mpr ⟨hzi0, hzT⟩) hzs p hp]
        exact ⟨x0, hx0, by simp⟩
    · intro v hv
      simp only [decide_eq_true_eq]
      constructor
      · rintro (rfl | hvB)
        · rfl
        · exfalso
          have : v ∈ B s p ∩ L s := Finset.mem_inter.mpr ⟨hvB, hv⟩
          rw [hdisj] at this
          exact Finset.notMem_empty v this
      · intro hvp
        exact Or.inl hvp
  · intro s s' hs hs' hss' ⟨⟨p, hp, a, ha⟩, ⟨p', hp', b, hb⟩⟩
    have hps : p ∈ L s := (Finset.mem_sdiff.mp hp).1
    have hp's' : p' ∈ L s' := (Finset.mem_sdiff.mp hp').1
    obtain ⟨haB, haLs'⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbB, hbLs⟩ := Finset.mem_inter.mp hb
    have haT : a ∈ T0 := rotor_sub_T0 hinter hmem hx0 hB1 hB2 hs hps haB
    have hbT : b ∈ T0 := rotor_sub_T0 hinter hmem hx0 hB1 hB2 hs' hp's' hbB
    have hBs : B s p = if p = b then (∅ : Finset (Fin N)) else {sigma b} :=
      hB1 s hs p hps b hbT hbLs
    have ha_eq : a = sigma b := by
      rw [hBs] at haB
      split_ifs at haB with hpb
      · exact False.elim (Finset.notMem_empty a haB)
      · exact Finset.mem_singleton.mp haB
    have hBs' : B s' p' = if p' = a then (∅ : Finset (Fin N)) else {sigma a} :=
      hB1 s' hs' p' hp's' a haT haLs'
    have hb_eq : b = sigma a := by
      rw [hBs'] at hbB
      split_ifs at hbB with hp'a
      · exact False.elim (Finset.notMem_empty b hbB)
      · exact Finset.mem_singleton.mp hbB
    have h2 : sigma (sigma b) = b := by rw [← ha_eq, ← hb_eq]
    exact sigma_sigma_ne hm hT0card htrans hbT h2

end PEqualNP.Outside.L_meta_1583

theorem PEqualNP.Outside.L_meta_1583 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  exact PEqualNP.Outside.L_meta_1583.main
