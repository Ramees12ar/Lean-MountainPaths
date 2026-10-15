import Mathlib

/-!
# Mountain paths: returns and peaks

A mountain path of size `n` (a Dyck path) is an up/down walk of `2n` steps that starts and ends at
height `0` and never goes below `0`. We prove:

* (a) the number of paths with exactly `k` returns to `0` is `k/(2n-k) * C(2n-k, n)`;
* (b) the variance of the number of returns is `2n(n-1)(2n+1)/((n+2)^2 (n+3))`;
* (c) the number of paths with exactly `k` peaks is the Narayana number `C(n,k) C(n,k-1) / n`;
* (d) the variance of the number of peaks is `(n-1)(n+1)/(4(2n-1))`.

Method. Instead of cutting a path at its returns, we build every walk step by step, adding one
step at the end (`Fin.snoc`). This gives recurrences for weighted sums over walks of any length
`L` that stay at or above `0` and end at height `H` (`Ws` for returns, `Ps` for peaks, split by the
last step). The recurrences are solved in closed form by induction on `L`, using Pascal's rule
for a binomial coefficient on the integers (`cz`) and the ballot numbers `Bal`.
References: E. Deutsch, "Dyck path enumeration", Discrete Math. 204 (1999);
R. P. Stanley, Enumerative Combinatorics, Vol. 2.
-/

set_option linter.unusedSectionVars false

open Finset

/-- Height after the first `i` steps (`true` is an up step). -/
def heightAt (n : ℕ) (w : Fin (2 * n) → Bool) (i : ℕ) : ℤ :=
  ∑ j : Fin (2 * n), if j.val < i then (if w j then 1 else -1) else 0

def mountainPaths (n : ℕ) : Finset (Fin (2 * n) → Bool) :=
  univ.filter fun w => heightAt n w (2 * n) = 0 ∧ ∀ i : Fin (2 * n + 1), 0 ≤ heightAt n w i.val

def returnCount (n : ℕ) (w : Fin (2 * n) → Bool) : ℕ :=
  ((Icc 1 (2 * n)).filter fun i => heightAt n w i = 0).card

def peakCount (n : ℕ) (w : Fin (2 * n) → Bool) : ℕ :=
  (univ.filter fun j : Fin (2 * n) =>
    ∃ h : j.val + 1 < 2 * n, w j = true ∧ w ⟨j.val + 1, h⟩ = false).card

def pathMean (n : ℕ) (f : (Fin (2 * n) → Bool) → ℚ) : ℚ :=
  (∑ w ∈ mountainPaths n, f w) / ((mountainPaths n).card : ℚ)

namespace MPAux

/-! ### Walks of any length -/

/-- Height after the first `i` steps (`true` is an up step). -/
def hgt (L : ℕ) (w : Fin L → Bool) (i : ℕ) : ℤ :=
  ∑ j : Fin L, if j.val < i then (if w j then 1 else -1) else 0

/-- The walk never goes below height `0`. -/
def nonneg (L : ℕ) (w : Fin L → Bool) : Prop := ∀ i : Fin (L + 1), 0 ≤ hgt L w i.val

instance (L : ℕ) : DecidablePred (nonneg L) := fun w => by unfold nonneg; infer_instance

/-- Number of returns to height `0` after the start. -/
def ret (L : ℕ) (w : Fin L → Bool) : ℕ := ((Icc 1 L).filter fun i => hgt L w i = 0).card

/-- Number of peaks (an up step followed right away by a down step). -/
def pk (L : ℕ) (w : Fin L → Bool) : ℕ :=
  (univ.filter fun j : Fin L => ∃ h : j.val + 1 < L, w j = true ∧ w ⟨j.val + 1, h⟩ = false).card

/-- Whether the last step is an up step (`false` for the empty walk). -/
def lastU : (L : ℕ) → (Fin L → Bool) → Bool
  | 0, _ => false
  | L + 1, w => w (Fin.last L)

/-- Value of one step. -/
def st (b : Bool) : ℤ := if b then 1 else -1

@[simp] lemma st_true : st true = 1 := rfl
@[simp] lemma st_false : st false = -1 := rfl

/-- Add one step at the end. -/
def snocw {L : ℕ} (w : Fin L → Bool) (b : Bool) : Fin (L + 1) → Bool := Fin.snoc w b

lemma snocw_castSucc {L : ℕ} (w : Fin L → Bool) (b : Bool) (j : Fin L) :
    snocw w b j.castSucc = w j := by
  simp [snocw]

lemma snocw_last {L : ℕ} (w : Fin L → Bool) (b : Bool) : snocw w b (Fin.last L) = b := by
  simp [snocw]

lemma hgt_snoc (L : ℕ) (w : Fin L → Bool) (b : Bool) (i : ℕ) :
    hgt (L + 1) (snocw w b) i = hgt L w i + (if L < i then st b else 0) := by
  unfold hgt
  rw [Fin.sum_univ_castSucc]
  simp only [snocw_castSucc, Fin.val_castSucc, snocw_last, Fin.val_last, st]

lemma hgt_ge (L : ℕ) (w : Fin L → Bool) {i : ℕ} (hi : L ≤ i) : hgt L w i = hgt L w L := by
  unfold hgt
  refine sum_congr rfl fun j _ => ?_
  rw [if_pos (by omega), if_pos j.isLt]

lemma hgt_zero_left (w : Fin 0 → Bool) (i : ℕ) : hgt 0 w i = 0 := by simp [hgt]

lemma hgt_le (L : ℕ) (w : Fin L → Bool) : hgt L w L ≤ L := by
  unfold hgt
  calc ∑ j : Fin L, (if j.val < L then (if w j then (1 : ℤ) else -1) else 0)
      ≤ ∑ _j : Fin L, (1 : ℤ) := sum_le_sum fun j _ => by split_ifs <;> norm_num
    _ = L := by simp

lemma hgt_snoc_end (L : ℕ) (w : Fin L → Bool) (b : Bool) :
    hgt (L + 1) (snocw w b) (L + 1) = hgt L w L + st b := by
  rw [hgt_snoc, if_pos (by omega), hgt_ge L w (by omega)]

lemma nonneg_end {L : ℕ} {w : Fin L → Bool} (h : nonneg L w) : 0 ≤ hgt L w L :=
  h ⟨L, by omega⟩

lemma nonneg_snoc (L : ℕ) (w : Fin L → Bool) (b : Bool) :
    nonneg (L + 1) (snocw w b) ↔ nonneg L w ∧ 0 ≤ hgt L w L + st b := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := i.isLt
      have := h ⟨i.val, by omega⟩
      simp only [hgt_snoc] at this
      rwa [if_neg (show ¬ L < i.val by omega), add_zero] at this
    · have := h ⟨L + 1, by omega⟩
      rw [hgt_snoc_end] at this
      exact this
  · rintro ⟨h1, h2⟩ i
    rcases Nat.lt_or_ge i.val (L + 1) with hi | hi
    · rw [hgt_snoc, if_neg (show ¬ L < i.val by omega), add_zero]; exact h1 ⟨i.val, hi⟩
    · rw [show i.val = L + 1 by omega, hgt_snoc_end]; exact h2

lemma ret_snoc (L : ℕ) (w : Fin L → Bool) (b : Bool) :
    ret (L + 1) (snocw w b) = ret L w + if hgt L w L + st b = 0 then 1 else 0 := by
  unfold ret
  rw [card_filter, card_filter, Finset.sum_Icc_succ_top (by omega), hgt_snoc_end]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi' := (mem_Icc.1 hi).2
  rw [hgt_snoc, if_neg (show ¬ L < i by omega), add_zero]

lemma lastU_snoc (L : ℕ) (w : Fin L → Bool) (b : Bool) : lastU (L + 1) (snocw w b) = b := by
  simp [lastU, snocw_last]

lemma pk_snoc (L : ℕ) (w : Fin L → Bool) (b : Bool) :
    pk (L + 1) (snocw w b) = pk L w + if lastU L w = true ∧ b = false then 1 else 0 := by
  unfold pk
  rw [card_filter, card_filter, Fin.sum_univ_castSucc]
  have hlast : ¬ ∃ h : (Fin.last L).val + 1 < L + 1, snocw w b (Fin.last L) = true ∧
      snocw w b ⟨(Fin.last L).val + 1, h⟩ = false := by
    rintro ⟨h, -⟩; simp at h
  rw [if_neg hlast, add_zero]
  cases L with
  | zero =>
    rw [Finset.univ_eq_empty, sum_empty, sum_empty]
    simp only [lastU, Bool.false_eq_true, false_and, if_false, add_zero]
  | succ M =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hold : ¬ ∃ h : (Fin.last M).val + 1 < M + 1, w (Fin.last M) = true ∧
        w ⟨(Fin.last M).val + 1, h⟩ = false := by
      rintro ⟨h, -⟩; simp at h
    rw [if_neg hold, add_zero]
    have hnew : (∃ h : (Fin.castSucc (Fin.last M)).val + 1 < M + 1 + 1,
        snocw w b (Fin.last M).castSucc = true ∧
        snocw w b ⟨(Fin.castSucc (Fin.last M)).val + 1, h⟩ = false) ↔
        (lastU (M + 1) w = true ∧ b = false) := by
      simp only [Fin.val_castSucc, Fin.val_last, snocw_castSucc, lastU]
      constructor
      · rintro ⟨h, h1, h2⟩
        refine ⟨h1, ?_⟩
        have : (⟨M + 1, h⟩ : Fin (M + 1 + 1)) = Fin.last (M + 1) := rfl
        rw [this, snocw_last] at h2
        exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨by omega, h1, ?_⟩
        have : (⟨M + 1, by omega⟩ : Fin (M + 1 + 1)) = Fin.last (M + 1) := rfl
        rw [this, snocw_last]; exact h2
    rw [if_congr hnew rfl rfl]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    apply if_congr _ rfl rfl
    simp only [Fin.val_castSucc, snocw_castSucc]
    constructor
    · rintro ⟨h, h1, h2⟩
      refine ⟨by omega, h1, ?_⟩
      have : (⟨j.val + 1, h⟩ : Fin (M + 1 + 1)) = Fin.castSucc ⟨j.val + 1, by omega⟩ := rfl
      rw [this, snocw_castSucc] at h2
      exact h2
    · rintro ⟨h, h1, h2⟩
      refine ⟨by omega, h1, ?_⟩
      have : (⟨j.val + 1, by omega⟩ : Fin (M + 1 + 1)) = Fin.castSucc ⟨j.val + 1, h⟩ := rfl
      rw [this, snocw_castSucc]; exact h2

/-- A sum over walks of length `L + 1` is a sum over walks of length `L` and a last step. -/
lemma sum_snoc {M : Type*} [AddCommMonoid M] (L : ℕ) (F : (Fin (L + 1) → Bool) → M) :
    ∑ w, F w = ∑ w : Fin L → Bool, (F (snocw w true) + F (snocw w false)) := by
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← sum_add_distrib]
  rfl

/-! ### Sums over walks with a given final height -/

/-- Sum of `f (number of returns)` over the walks of length `L` that stay at or above `0` and end
at height `H`. -/
noncomputable def Ws (L : ℕ) (H : ℤ) (f : ℕ → ℤ) : ℤ :=
  ∑ w : Fin L → Bool, if nonneg L w ∧ hgt L w L = H then f (ret L w) else 0

/-- Sum of `f (number of peaks)` over such walks whose last step is `u`. -/
noncomputable def Ps (L : ℕ) (H : ℤ) (u : Bool) (f : ℕ → ℤ) : ℤ :=
  ∑ w : Fin L → Bool, if nonneg L w ∧ hgt L w L = H ∧ lastU L w = u then f (pk L w) else 0

lemma Ws_zero (H : ℤ) (f : ℕ → ℤ) : Ws 0 H f = if H = 0 then f 0 else 0 := by
  unfold Ws
  rw [Fintype.sum_unique]
  have hn : nonneg 0 (default : Fin 0 → Bool) := fun i => by rw [hgt_zero_left]
  have hr : ∀ w : Fin 0 → Bool, ret 0 w = 0 := fun w => by simp [ret]
  rw [hgt_zero_left, hr]
  by_cases hH : H = 0
  · rw [if_pos ⟨hn, hH.symm⟩, if_pos hH]
  · rw [if_neg (fun h => hH h.2.symm), if_neg hH]

lemma Ps_zero (H : ℤ) (u : Bool) (f : ℕ → ℤ) :
    Ps 0 H u f = if H = 0 ∧ u = false then f 0 else 0 := by
  unfold Ps
  rw [Fintype.sum_unique]
  have hn : nonneg 0 (default : Fin 0 → Bool) := fun i => by rw [hgt_zero_left]
  have hp : ∀ w : Fin 0 → Bool, pk 0 w = 0 := fun w => by unfold pk; simp
  have hl : ∀ w : Fin 0 → Bool, lastU 0 w = false := fun w => rfl
  rw [hgt_zero_left, hp, hl]
  by_cases hH : H = 0 <;> by_cases hu : u = false
  · rw [if_pos ⟨hn, hH.symm, hu.symm⟩, if_pos ⟨hH, hu⟩]
  · rw [if_neg (fun h => hu h.2.2.symm), if_neg (fun h => hu h.2)]
  · rw [if_neg (fun h => hH h.2.1.symm), if_neg (fun h => hH h.1)]
  · rw [if_neg (fun h => hH h.2.1.symm), if_neg (fun h => hH h.1)]

lemma Ws_neg (L : ℕ) {H : ℤ} (hH : H < 0) (f : ℕ → ℤ) : Ws L H f = 0 := by
  unfold Ws
  refine sum_eq_zero fun w _ => if_neg fun h => ?_
  have := nonneg_end h.1; omega

lemma Ws_big (L : ℕ) {H : ℤ} (hH : (L : ℤ) < H) (f : ℕ → ℤ) : Ws L H f = 0 := by
  unfold Ws
  refine sum_eq_zero fun w _ => if_neg fun h => ?_
  have := hgt_le L w; omega

lemma Ps_neg (L : ℕ) {H : ℤ} (hH : H < 0) (u : Bool) (f : ℕ → ℤ) : Ps L H u f = 0 := by
  unfold Ps
  refine sum_eq_zero fun w _ => if_neg fun h => ?_
  have := nonneg_end h.1; omega

lemma Ps_big (L : ℕ) {H : ℤ} (hH : (L : ℤ) < H) (u : Bool) (f : ℕ → ℤ) : Ps L H u f = 0 := by
  unfold Ps
  refine sum_eq_zero fun w _ => if_neg fun h => ?_
  have := hgt_le L w; omega

/-- Step rule for `Ws`. -/
lemma Ws_succ (L : ℕ) (H : ℤ) (f : ℕ → ℤ) :
    Ws (L + 1) H f = Ws L (H - 1) f +
      (if 0 ≤ H then Ws L (H + 1) (fun r => f (r + if H = 0 then 1 else 0)) else 0) := by
  unfold Ws
  rw [sum_snoc, sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun w _ => ?_
    simp only [nonneg_snoc, hgt_snoc_end, ret_snoc, st_true]
    by_cases hn : nonneg L w
    · have h0 := nonneg_end hn
      have e1 : (hgt L w L + 1 = H) ↔ (hgt L w L = H - 1) := by omega
      have e2 : ¬ (hgt L w L + 1 = 0) := by omega
      have e3 : 0 ≤ hgt L w L + 1 := by omega
      simp [hn, e1, e2, e3]
    · simp [hn]
  · by_cases hH0 : 0 ≤ H
    · rw [if_pos hH0]
      refine sum_congr rfl fun w _ => ?_
      simp only [nonneg_snoc, hgt_snoc_end, ret_snoc, st_false]
      by_cases hn : nonneg L w
      · by_cases hH : hgt L w L = H + 1
        · have e1 : hgt L w L + -1 = H := by omega
          have e3 : 0 ≤ hgt L w L + -1 := by omega
          have e4 : (hgt L w L + -1 = 0) ↔ (H = 0) := by omega
          simp [hn, hH, e1, e3, e4, show ¬ H < 0 by omega]
        · have e1 : ¬ (hgt L w L + -1 = H) := by omega
          simp [hn, hH, e1]
      · simp [hn]
    · rw [if_neg hH0]
      refine sum_eq_zero fun w _ => ?_
      simp only [nonneg_snoc, hgt_snoc_end, st_false]
      rw [if_neg (fun h => by omega)]

/-- Step rule for `Ps`, last step up. -/
lemma Ps_succ_true (L : ℕ) (H : ℤ) (f : ℕ → ℤ) :
    Ps (L + 1) H true f = Ps L (H - 1) true f + Ps L (H - 1) false f := by
  unfold Ps
  rw [sum_snoc, ← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  simp only [nonneg_snoc, hgt_snoc_end, lastU_snoc, pk_snoc, st_true, st_false]
  by_cases hn : nonneg L w
  · have h0 := nonneg_end hn
    have e1 : (hgt L w L + 1 = H) ↔ (hgt L w L = H - 1) := by omega
    have e3 : 0 ≤ hgt L w L + 1 := by omega
    rcases Bool.eq_false_or_eq_true (lastU L w) with hu | hu <;> simp [hn, hu, e1, e3]
  · simp [hn]

/-- Step rule for `Ps`, last step down. -/
lemma Ps_succ_false (L : ℕ) (H : ℤ) (f : ℕ → ℤ) :
    Ps (L + 1) H false f = if 0 ≤ H then
      Ps L (H + 1) true (fun p => f (p + 1)) + Ps L (H + 1) false f else 0 := by
  unfold Ps
  rw [sum_snoc]
  by_cases hH0 : 0 ≤ H
  · rw [if_pos hH0, ← sum_add_distrib]
    refine sum_congr rfl fun w _ => ?_
    simp only [nonneg_snoc, hgt_snoc_end, lastU_snoc, pk_snoc, st_true, st_false]
    by_cases hn : nonneg L w
    · by_cases hH : hgt L w L = H + 1
      · have e1 : hgt L w L + -1 = H := by omega
        have e3 : 0 ≤ hgt L w L + -1 := by omega
        rcases Bool.eq_false_or_eq_true (lastU L w) with hu | hu <;>
          simp [hn, hH, hu, e1, e3, show ¬ H < 0 by omega]
      · have e1 : ¬ (hgt L w L + -1 = H) := by omega
        simp [hn, hH, e1]
    · simp [hn]
  · rw [if_neg hH0]
    refine sum_eq_zero fun w _ => ?_
    simp only [nonneg_snoc, hgt_snoc_end, lastU_snoc, st_true, st_false]
    have : ¬ (0 ≤ hgt L w L + -1 ∧ hgt L w L + -1 = H) := fun h => by omega
    simp only [Bool.true_eq_false, and_false, if_false, zero_add]
    rw [if_neg (fun h => this ⟨h.1.2, h.2.1⟩)]

end MPAux

namespace MPAux

/-! ### A binomial coefficient that is `0` outside the usual range -/

def cz (n k : ℤ) : ℤ := if 0 ≤ k ∧ k ≤ n then (Nat.choose n.toNat k.toNat : ℤ) else 0

lemma cz_nat (m j : ℕ) : cz m j = (m.choose j : ℤ) := by
  unfold cz
  by_cases h : j ≤ m
  · rw [if_pos ⟨by omega, by omega⟩]; simp
  · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma cz_neg {n k : ℤ} (h : k < 0) : cz n k = 0 := by unfold cz; rw [if_neg (by omega)]

lemma cz_gt {n k : ℤ} (h : n < k) : cz n k = 0 := by unfold cz; rw [if_neg (by omega)]

lemma cz_negn {n k : ℤ} (h : n < 0) : cz n k = 0 := by unfold cz; rw [if_neg (by omega)]

@[simp] lemma cz_m1 (n : ℤ) : cz n (-1) = 0 := cz_neg (by norm_num)

@[simp] lemma cz_m1l (k : ℤ) : cz (-1) k = 0 := cz_negn (by norm_num)

lemma cz_pascal (n k : ℤ) (hn : 1 ≤ n) : cz n k = cz (n - 1) k + cz (n - 1) (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [cz_neg hk, cz_neg hk, cz_neg (by omega)]; simp
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [show ((m : ℤ) + 1 - 1) = (m : ℕ) by ring, show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num,
      cz_neg (by norm_num : (-1 : ℤ) < 0), show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      cz_nat, cz_nat]
    simp
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show ((m : ℤ) + 1 - 1) = (m : ℕ) by ring, show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℕ) by push_cast; ring,
      show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, cz_nat, cz_nat, cz_nat,
      Nat.choose_succ_succ]
    push_cast; ring

lemma cz_symm (n k : ℤ) (hn : 0 ≤ n) : cz n k = cz n (n - k) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [cz_neg hk, cz_gt (by omega)]
  rcases lt_or_ge (m : ℤ) k with hk' | hk'
  · rw [cz_gt hk', cz_neg (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
  rw [show (m : ℤ) - j = ((m - j : ℕ) : ℤ) by push_cast [show j ≤ m by omega]; ring, cz_nat, cz_nat,
    Nat.choose_symm (by omega)]

/-! ### Ballot numbers -/

/-- Number of walks with `x` up steps and `y` down steps that never go below `0`. -/
def Bal (x y : ℤ) : ℤ := cz (x + y) x - cz (x + y) (x + 1)

lemma Bal_pascal (x y : ℤ) (h : 1 ≤ x + y) : Bal x y = Bal (x - 1) y + Bal x (y - 1) := by
  unfold Bal
  rw [cz_pascal (x + y) x h, cz_pascal (x + y) (x + 1) h,
    show x - 1 + y = x + y - 1 by ring, show x + (y - 1) = x + y - 1 by ring,
    show x - 1 + 1 = x by ring, show x + 1 - 1 = x by ring]
  ring

lemma Bal_neg (x y : ℤ) (hx : 0 ≤ x) (hy : y < 0) : Bal x y = 0 := by
  unfold Bal; rw [cz_gt (by omega), cz_gt (by omega)]; simp

lemma Bal_zero (x : ℤ) (hx : 0 ≤ x) : Bal x 0 = 1 := by
  unfold Bal
  rw [add_zero, cz_gt (show x < x + 1 by omega)]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, x = m := ⟨x.toNat, by omega⟩
  rw [cz_nat]; simp

lemma Bal_succ (x : ℤ) (hx : 0 ≤ x) : Bal x (x + 1) = 0 := by
  unfold Bal
  rw [cz_symm (x + (x + 1)) x (by omega), show x + (x + 1) - x = x + 1 by ring]
  ring

/-! ### Returns: distribution and moments -/

/-- Closed form for the number of walks with `a` ups, `b` downs and exactly `k` returns. -/
def RD (a b k : ℕ) : ℤ := if a = 0 then (if b = 0 ∧ k = 0 then 1 else 0) else Bal (a - 1) (b - k)

lemma Ws_zero_fn (L : ℕ) (H : ℤ) : Ws L H (fun _ => 0) = 0 := by simp [Ws]

lemma Ws_add (L : ℕ) (H : ℤ) (f g : ℕ → ℤ) :
    Ws L H (fun r => f r + g r) = Ws L H f + Ws L H g := by
  unfold Ws; rw [← sum_add_distrib]
  exact sum_congr rfl fun w _ => by split_ifs <;> ring

lemma Ws_smul (L : ℕ) (H : ℤ) (c : ℤ) (f : ℕ → ℤ) :
    Ws L H (fun r => c * f r) = c * Ws L H f := by
  unfold Ws; rw [mul_sum]
  exact sum_congr rfl fun w _ => by split_ifs <;> ring

lemma ind_shift (k : ℕ) :
    (fun r : ℕ => if r + 1 = k then (1 : ℤ) else 0) =
      if k = 0 then (fun _ => 0) else (fun r => if r = k - 1 then 1 else 0) := by
  funext r
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    show (if r + 1 = k then (1 : ℤ) else 0) = if r = k - 1 then 1 else 0
    by_cases h : r = k - 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]

theorem ret_dist : ∀ L a b k : ℕ, a + b = L → b ≤ a →
    Ws L ((a : ℤ) - b) (fun r => if r = k then 1 else 0) = RD a b k := by
  intro L
  induction L with
  | zero =>
    intro a b k hab hba
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    rw [Ws_zero]; unfold RD; simp [eq_comm]
  | succ L ih =>
    intro a b k hab hba
    have ha : 1 ≤ a := by omega
    rw [Ws_succ, if_pos (by omega)]
    have hRD : RD a b k = Bal ((a : ℤ) - 1) ((b : ℤ) - k) := by
      unfold RD; rw [if_neg (by omega)]
    rw [hRD]
    by_cases hab' : a = b
    · subst hab'
      rw [Ws_neg L (by omega), zero_add, if_pos (by simp)]
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      have hL : c + 1 + c = L := by omega
      rw [show ((c + 1 : ℕ) : ℤ) - (c + 1 : ℕ) + 1 = ((c + 1 : ℕ) : ℤ) - (c : ℕ) by push_cast; ring,
        ind_shift]
      by_cases hk : k = 0
      · subst hk
        rw [if_pos rfl, Ws_zero_fn]
        push_cast
        rw [show ((c : ℤ) + 1 - 0) = (c : ℤ) + 1 by ring, show (c : ℤ) + 1 - 1 = c by ring,
          Bal_succ c (by omega)]
      · rw [if_neg hk, ih (c + 1) c (k - 1) hL (by omega)]
        unfold RD
        rw [if_neg (by omega)]
        push_cast [show 1 ≤ k by omega]
        ring_nf
    · rw [show (a : ℤ) - b - 1 = ((a - 1 : ℕ) : ℤ) - b by push_cast [ha]; ring,
        ih (a - 1) b k (by omega) (by omega)]
      have hz : ¬ ((a : ℤ) - b = 0) := by omega
      simp only [hz, if_false, add_zero]
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · rw [Ws_big L (by push_cast; omega), add_zero]
        unfold RD
        by_cases ha1 : a - 1 = 0
        · rw [if_pos ha1]
          obtain rfl : a = 1 := by omega
          by_cases hk : k = 0
          · subst hk; simp [Bal_zero]
          · rw [if_neg (by omega)]
            push_cast
            rw [Bal_neg 0 _ le_rfl (by omega)]
        · rw [if_neg ha1]
          push_cast [ha]
          by_cases hk : k = 0
          · subst hk; simp only [CharP.cast_eq_zero, sub_zero]
            rw [Bal_zero _ (by omega), Bal_zero _ (by omega)]
          · rw [Bal_neg _ _ (by omega) (by omega), Bal_neg _ _ (by omega) (by omega)]
      · rw [show (a : ℤ) - b + 1 = (a : ℤ) - ((b - 1 : ℕ) : ℤ) by push_cast [hb]; ring,
          ih a (b - 1) k (by omega) (by omega)]
        unfold RD
        rw [if_neg (show ¬ a - 1 = 0 by omega), if_neg (show ¬ a = 0 by omega)]
        push_cast [ha, hb]
        rcases le_or_gt k b with hkb | hkb
        · rw [Bal_pascal ((a : ℤ) - 1) ((b : ℤ) - k) (by omega)]
          ring_nf
        · repeat rw [Bal_neg _ _ (by omega) (by omega)]
          all_goals ring_nf

/-- Closed forms for `∑ 1`, `∑ r` and `∑ r²` over walks with `a` ups and `b` downs. -/
theorem ret_moments : ∀ L a b : ℕ, a + b = L → b ≤ a →
    Ws L ((a : ℤ) - b) (fun _ => 1) = Bal a b ∧
    Ws L ((a : ℤ) - b) (fun r => (r : ℤ)) = Bal (a + 1) (b - 1) ∧
    Ws L ((a : ℤ) - b) (fun r => (r : ℤ) ^ 2) = 2 * Bal (a + 2) (b - 2) + Bal (a + 1) (b - 1) := by
  intro L
  induction L with
  | zero =>
    intro a b hab hba
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp only [Ws_zero, Nat.cast_zero, sub_self, if_true]
    refine ⟨by rw [Bal_zero 0 le_rfl], ?_, ?_⟩
    · rw [Bal_neg _ _ (by norm_num) (by norm_num)]
    · rw [Bal_neg _ _ (by norm_num) (by norm_num), Bal_neg _ _ (by norm_num) (by norm_num)]; simp
  | succ L ih =>
    intro a b hab hba
    have ha : 1 ≤ a := by omega
    simp only [Ws_succ, if_pos (show (0 : ℤ) ≤ (a : ℤ) - b by omega)]
    -- the two neighbours
    have T1 : ∀ f : ℕ → ℤ, Ws L ((a : ℤ) - b - 1) f =
        if a = b then 0 else Ws L (((a - 1 : ℕ) : ℤ) - b) f := fun f => by
      by_cases h : a = b
      · rw [if_pos h, Ws_neg L (by omega)]
      · rw [if_neg h, show ((a - 1 : ℕ) : ℤ) - b = (a : ℤ) - b - 1 by push_cast [ha]; ring]
    have T2 : ∀ f : ℕ → ℤ, Ws L ((a : ℤ) - b + 1) f =
        if b = 0 then 0 else Ws L ((a : ℤ) - ((b - 1 : ℕ) : ℤ)) f := fun f => by
      by_cases h : b = 0
      · rw [if_pos h, Ws_big L (by subst h; push_cast; omega)]
      · rw [if_neg h, show (a : ℤ) - ((b - 1 : ℕ) : ℤ) = (a : ℤ) - b + 1 by push_cast [show 1 ≤ b by omega]; ring]
    rw [T1, T1, T1, T2, T2, T2]
    have hz : ((a : ℤ) - b = 0) ↔ a = b := by omega
    by_cases hab' : a = b
    · subst hab'
      have hb : 1 ≤ a := ha
      simp only [if_true, zero_add, if_neg (show ¬ a = 0 by omega), sub_self]
      obtain ⟨I0, I1, I2⟩ := ih a (a - 1) (by omega) (by omega)
      have e1 : (fun r : ℕ => (((r + 1 : ℕ)) : ℤ)) = (fun r : ℕ => (r : ℤ) + 1) := by
        funext r; push_cast; ring
      have e2 : (fun r : ℕ => (((r + 1 : ℕ)) : ℤ) ^ 2) =
          (fun r : ℕ => (r : ℤ) ^ 2 + 2 * (r : ℤ) + 1) := by
        funext r; push_cast; ring
      simp only [if_true] at *
      refine ⟨?_, ?_, ?_⟩
      · rw [I0]; push_cast [hb]
        rw [Bal_pascal (a : ℤ) (a : ℤ) (by omega), show (a : ℤ) - 1 = (a : ℤ) - 1 from rfl]
        rw [show Bal ((a : ℤ) - 1) (a : ℤ) = 0 by
          simpa using Bal_succ ((a : ℤ) - 1) (by omega)]
        ring
      · rw [e1, Ws_add, I1, I0]; push_cast [hb]
        rw [Bal_pascal ((a : ℤ) + 1) ((a : ℤ) - 1) (by omega)]
        ring_nf
      · rw [e2, Ws_add, Ws_add, Ws_smul, I2, I1, I0]; push_cast [hb]
        rw [Bal_pascal ((a : ℤ) + 2) ((a : ℤ) - 2) (by omega),
          Bal_pascal ((a : ℤ) + 1) ((a : ℤ) - 1) (by omega)]
        ring_nf
    · simp only [if_neg hab', show ¬ ((a : ℤ) - b = 0) by omega, if_false, add_zero]
      obtain ⟨J0, J1, J2⟩ := ih (a - 1) b (by omega) (by omega)
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp only [if_true, add_zero]
        rw [J0, J1, J2]; push_cast [ha]
        refine ⟨?_, ?_, ?_⟩
        · rw [Bal_zero _ (by omega), Bal_zero _ (by omega)]
        · rw [Bal_neg _ _ (by omega) (by norm_num), Bal_neg _ _ (by omega) (by norm_num)]
        · rw [Bal_neg _ _ (by omega) (by norm_num), Bal_neg _ _ (by omega) (by norm_num),
            Bal_neg _ _ (by omega) (by norm_num), Bal_neg _ _ (by omega) (by norm_num)]
      · simp only [if_neg (show ¬ b = 0 by omega)]
        obtain ⟨K0, K1, K2⟩ := ih a (b - 1) (by omega) (by omega)
        rw [J0, J1, J2, K0, K1, K2]; push_cast [ha, hb]
        refine ⟨?_, ?_, ?_⟩
        · rw [Bal_pascal (a : ℤ) (b : ℤ) (by omega)]
        · rw [Bal_pascal ((a : ℤ) + 1) ((b : ℤ) - 1) (by omega)]; ring_nf
        · rw [Bal_pascal ((a : ℤ) + 2) ((b : ℤ) - 2) (by omega),
            Bal_pascal ((a : ℤ) + 1) ((b : ℤ) - 1) (by omega)]
          ring_nf

/-! ### Peaks: distribution -/

def PUc (a b : ℕ) (k : ℤ) : ℤ :=
  if a = 0 then 0 else cz (a - 1) k * cz b k - cz a k * cz (b - 1) k

def PDc (a b : ℕ) (k : ℤ) : ℤ :=
  if a = 0 then (if b = 0 ∧ k = 0 then 1 else 0) else
    cz (a - 1) (k - 1) * cz b k - cz a (k - 1) * cz (b - 1) k

lemma Ps_zero_fn (L : ℕ) (H : ℤ) (u : Bool) : Ps L H u (fun _ => 0) = 0 := by simp [Ps]

lemma cz_zero_left (k : ℤ) : cz 0 k = if k = 0 then 1 else 0 := by
  unfold cz
  by_cases h : k = 0
  · subst h; simp
  · rw [if_neg (by omega), if_neg h]

theorem peak_dist : ∀ L a b k : ℕ, a + b = L → b ≤ a →
    Ps L ((a : ℤ) - b) true (fun p => if p = k then 1 else 0) = PUc a b k ∧
    Ps L ((a : ℤ) - b) false (fun p => if p = k then 1 else 0) = PDc a b k := by
  intro L
  induction L with
  | zero =>
    intro a b k hab hba
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp only [Ps_zero, PUc, PDc, Nat.cast_zero, sub_self, if_true]
    refine ⟨by simp, ?_⟩
    by_cases hk : k = 0 <;> simp [hk, eq_comm]
  | succ L ih =>
    intro a b k hab hba
    have ha : 1 ≤ a := by omega
    have hPU : PUc a b k = cz ((a : ℤ) - 1) k * cz b k - cz a k * cz ((b : ℤ) - 1) k := by
      unfold PUc; rw [if_neg (by omega)]
    have hPD : PDc a b k = cz ((a : ℤ) - 1) ((k : ℤ) - 1) * cz b k -
        cz a ((k : ℤ) - 1) * cz ((b : ℤ) - 1) k := by
      unfold PDc; rw [if_neg (by omega)]
    rw [hPU, hPD, Ps_succ_true, Ps_succ_false, if_pos (by omega)]
    constructor
    · by_cases hab' : a = b
      · subst hab'
        rw [Ps_neg L (by omega), Ps_neg L (by omega)]
        ring
      · rw [show (a : ℤ) - b - 1 = ((a - 1 : ℕ) : ℤ) - b by push_cast [ha]; ring]
        obtain ⟨U1, D1⟩ := ih (a - 1) b k (by omega) (by omega)
        rw [U1, D1]
        unfold PUc PDc
        by_cases ha1 : a - 1 = 0
        · obtain rfl : a = 1 := by omega
          obtain rfl : b = 0 := by omega
          simp only [if_true, true_and, Nat.cast_one, Nat.cast_zero, sub_self, zero_sub, cz_m1l,
            mul_zero, sub_zero, zero_add, cz_zero_left]
          by_cases hk : k = 0
          · subst hk; simp
          · simp [hk]
        · rw [if_neg ha1, if_neg ha1]
          push_cast [ha]
          rw [cz_pascal (a : ℤ) k (by omega), cz_pascal ((a : ℤ) - 1) k (by omega)]
          ring_nf
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · rw [Ps_big L (by push_cast; omega), Ps_big L (by push_cast; omega), add_zero]
        simp only [Nat.cast_zero, zero_sub, cz_m1l, mul_zero, sub_zero, cz_zero_left]
        by_cases hk : k = 0
        · subst hk; simp
        · simp [hk]
      · rw [show (a : ℤ) - b + 1 = (a : ℤ) - ((b - 1 : ℕ) : ℤ) by push_cast [hb]; ring]
        obtain ⟨U2, D2⟩ := ih a (b - 1) k (by omega) (by omega)
        rw [D2]
        have hshift : Ps L ((a : ℤ) - ((b - 1 : ℕ) : ℤ)) true
            (fun p => if p + 1 = k then 1 else 0) =
            cz ((a : ℤ) - 1) ((k : ℤ) - 1) * cz ((b - 1 : ℕ) : ℤ) ((k : ℤ) - 1) -
              cz a ((k : ℤ) - 1) * cz (((b - 1 : ℕ) : ℤ) - 1) ((k : ℤ) - 1) := by
          rw [ind_shift]
          by_cases hk : k = 0
          · subst hk; rw [if_pos rfl, Ps_zero_fn]
            simp
          · rw [if_neg hk, (ih a (b - 1) (k - 1) (by omega) (by omega)).1]
            unfold PUc
            rw [if_neg (by omega)]
            push_cast [show 1 ≤ k by omega]
            ring_nf
        rw [hshift]
        unfold PDc
        rw [if_neg (show ¬ a = 0 by omega)]
        push_cast [hb]
        by_cases hb1 : b = 1
        · subst hb1
          simp only [Nat.cast_one, sub_self, zero_sub, cz_m1l, mul_zero, sub_zero]
          rw [cz_pascal 1 (k : ℤ) le_rfl]
          simp only [sub_self, cz_zero_left]
          by_cases hk : k = 0
          · subst hk; simp
          · simp [hk]
        · rw [cz_pascal (b : ℤ) k (by omega), cz_pascal ((b : ℤ) - 1) k (by omega)]
          ring_nf

end MPAux

namespace MPAux

/-! ### Bridge from the task definitions to `Ws` and `Ps` -/

lemma mp_eq (n : ℕ) : mountainPaths n =
    univ.filter fun w => nonneg (2 * n) w ∧ hgt (2 * n) w (2 * n) = 0 := by
  ext w
  simp only [mountainPaths, mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma bridge_ret (n : ℕ) (f : ℕ → ℤ) :
    ∑ w ∈ mountainPaths n, f (returnCount n w) = Ws (2 * n) 0 f := by
  rw [mp_eq, sum_filter]; rfl

lemma bridge_pk (n : ℕ) (f : ℕ → ℤ) :
    ∑ w ∈ mountainPaths n, f (peakCount n w) = Ps (2 * n) 0 true f + Ps (2 * n) 0 false f := by
  rw [mp_eq, sum_filter]; unfold Ps; rw [← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  have hp : peakCount n w = pk (2 * n) w := rfl
  rw [hp]
  cases h : lastU (2 * n) w <;> simp [h]

lemma czN (m j : ℕ) {x y : ℤ} (hx : x = m) (hy : y = j) : cz x y = m.choose j := by
  subst hx hy; exact cz_nat m j

lemma balC (N p : ℕ) (x y : ℤ) (hs : x + y = N) (hx : x = p) :
    Bal x y = (N.choose p : ℤ) - N.choose (p + 1) := by
  unfold Bal
  rw [hs, hx, cz_nat, show (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ) by push_cast; ring, cz_nat]

/-! ### (a) returns -/

lemma card_ret (n k : ℕ) :
    (((mountainPaths n).filter fun w => returnCount n w = k).card : ℤ) = RD n n k := by
  rw [← ret_dist (2 * n) n n k (by ring) le_rfl, sub_self, ← bridge_ret]
  simp only [sum_boole]

/-- The binomial step behind (a). -/
lemma ret_identity (m j : ℕ) (hj : j ≤ m) :
    (((2 * m - j).choose m : ℤ) - (2 * m - j).choose (m + 1)) * ((2 * m - j : ℕ) + 1) =
      ((j : ℤ) + 1) * ((2 * m - j + 1).choose (m + 1) : ℕ) := by
  set M := 2 * m - j with hM
  have hMj : (M : ℤ) = 2 * m - j := by rw [hM]; push_cast [show j ≤ 2 * m by omega]; ring
  have h1 := Nat.add_one_mul_choose_eq M m
  have h2 := Nat.choose_succ_right_eq M m
  have h1' : ((M : ℤ) + 1) * (M.choose m : ℤ) = ((M + 1).choose (m + 1) : ℤ) * ((m : ℤ) + 1) := by
    exact_mod_cast h1
  have h2' : ((M.choose (m + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) = (M.choose m : ℤ) * ((M : ℤ) - m) := by
    rw [← Nat.cast_sub (by omega)]; exact_mod_cast h2
  apply mul_right_cancel₀ (show ((m : ℤ) + 1) ≠ 0 by positivity)
  linear_combination ((j : ℤ) + 1) * h1' - ((M : ℤ) + 1) * h2' - ((M : ℤ) + 1) * (M.choose m : ℤ) * hMj

end MPAux

open MPAux

theorem returns_count (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((mountainPaths n).filter fun w => returnCount n w = k).card * (2 * n - k) =
      k * (2 * n - k).choose n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := card_ret (m + 1) (j + 1)
  unfold RD at h
  rw [if_neg (by omega), balC (2 * m - j) m _ _ (by push_cast; omega) (by push_cast; ring)] at h
  rw [show 2 * (m + 1) - (j + 1) = 2 * m - j + 1 by omega]
  apply @Nat.cast_injective ℤ
  push_cast
  rw [h]
  have := ret_identity m j (by omega)
  push_cast at this
  rw [this]

namespace MPAux

/-! ### (c) peaks -/

lemma card_pk (n k : ℕ) :
    (((mountainPaths n).filter fun w => peakCount n w = k).card : ℤ) =
      PUc n n k + PDc n n k := by
  rw [← (peak_dist (2 * n) n n k (by ring) le_rfl).1, ← (peak_dist (2 * n) n n k (by ring) le_rfl).2,
    sub_self, ← bridge_pk]
  simp only [sum_boole]

/-- Number of walks of size `n` with exactly `k` peaks. -/
def Np (n k : ℕ) : ℕ := ((mountainPaths n).filter fun w => peakCount n w = k).card

lemma pk_core (m j : ℕ) :
    ((m : ℤ) + 1) * (Np (m + 1) (j + 1) : ℤ) =
      ((m + 1).choose (j + 1) : ℤ) * ((m + 1).choose j : ℤ) := by
  unfold Np
  rw [card_pk]
  have hU : PUc (m + 1) (m + 1) ((j + 1 : ℕ) : ℤ) = 0 := by unfold PUc; split_ifs <;> ring
  rw [hU, zero_add]
  unfold PDc
  rw [if_neg (by omega)]
  rw [czN m j (by push_cast; ring) (by push_cast; ring),
    czN (m + 1) (j + 1) (by push_cast; ring) (by push_cast; ring),
    czN (m + 1) j (by push_cast; ring) (by push_cast; ring),
    czN m (j + 1) (by push_cast; ring) (by push_cast; ring)]
  rcases le_or_gt j m with hjm | hjm
  · have h1 : ((m : ℤ) + 1) * (m.choose j : ℤ) = ((m + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    have h2 : (m.choose (j + 1) : ℤ) * ((j : ℤ) + 1) = (m.choose j : ℤ) * ((m : ℤ) - j) := by
      rw [← Nat.cast_sub hjm]; exact_mod_cast Nat.choose_succ_right_eq m j
    have h3 : ((m + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) =
        ((m + 1).choose j : ℤ) * ((m : ℤ) + 1 - j) := by
      rw [show (m : ℤ) + 1 - j = ((m + 1 - j : ℕ) : ℤ) by push_cast [show j ≤ m + 1 by omega]; ring]
      exact_mod_cast Nat.choose_succ_right_eq (m + 1) j
    apply mul_right_cancel₀ (show ((j : ℤ) + 1) ≠ 0 by positivity)
    linear_combination (((m : ℤ) + 1) * (m.choose j : ℤ)) * h3 -
      (((m : ℤ) + 1) * ((m + 1).choose j : ℤ)) * h2 + ((m + 1).choose j : ℤ) * h1
  · rw [Nat.choose_eq_zero_of_lt hjm, Nat.choose_eq_zero_of_lt (show m < j + 1 by omega),
      Nat.choose_eq_zero_of_lt (show m + 1 < j + 1 by omega)]
    simp

lemma Np_zero (m : ℕ) : Np (m + 1) 0 = 0 := by
  have h := card_pk (m + 1) 0
  unfold PUc PDc at h
  rw [if_neg (by omega), if_neg (by omega)] at h
  simp only [Nat.cast_zero, zero_sub, cz_m1, mul_zero, zero_mul, sub_self, add_zero] at h
  have h' : (Np (m + 1) 0 : ℤ) = 0 := by unfold Np; rw [h]; ring
  exact_mod_cast h'

end MPAux

theorem peaks_count (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    n * ((mountainPaths n).filter fun w => peakCount n w = k).card =
      n.choose k * n.choose (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := pk_core m j
  rw [Nat.add_sub_cancel]
  apply @Nat.cast_injective ℤ
  push_cast
  exact h

namespace MPAux

/-! ### Variance of returns -/

lemma choose_rel (N p : ℕ) (hp : p ≤ N) :
    ((N.choose (p + 1) : ℕ) : ℚ) * ((p : ℚ) + 1) = (N.choose p : ℚ) * ((N : ℚ) - p) := by
  rw [← Nat.cast_sub hp]; exact_mod_cast Nat.choose_succ_right_eq N p

theorem ret_var (n : ℕ) (hn : 1 ≤ n) :
    pathMean n (fun w => (returnCount n w : ℚ) ^ 2) -
        (pathMean n (fun w => (returnCount n w : ℚ))) ^ 2 =
      2 * (n : ℚ) * (n - 1) * (2 * n + 1) / ((n + 2) ^ 2 * (n + 3)) := by
  obtain ⟨M0, M1, M2⟩ := ret_moments (2 * n) n n (by ring) le_rfl
  rw [sub_self] at M0 M1 M2
  rw [balC (2 * n) n _ _ (by push_cast; ring) rfl] at M0
  rw [balC (2 * n) (n + 1) ((n : ℤ) + 1) ((n : ℤ) - 1) (by push_cast; ring) (by push_cast; ring)]
    at M1 M2
  rw [balC (2 * n) (n + 2) ((n : ℤ) + 2) ((n : ℤ) - 2) (by push_cast; ring) (by push_cast; ring)]
    at M2
  have A0 : ((mountainPaths n).card : ℚ) =
      ((2 * n).choose n : ℚ) - (2 * n).choose (n + 1) := by
    have := bridge_ret n (fun _ => 1)
    rw [M0, sum_const, nsmul_eq_mul, mul_one] at this
    exact_mod_cast this
  have A1 : ∑ w ∈ mountainPaths n, (returnCount n w : ℚ) =
      ((2 * n).choose (n + 1) : ℚ) - (2 * n).choose (n + 1 + 1) := by
    have := bridge_ret n (fun r => (r : ℤ))
    rw [M1] at this
    exact_mod_cast this
  have A2 : ∑ w ∈ mountainPaths n, (returnCount n w : ℚ) ^ 2 =
      2 * (((2 * n).choose (n + 2) : ℚ) - (2 * n).choose (n + 2 + 1)) +
        (((2 * n).choose (n + 1) : ℚ) - (2 * n).choose (n + 1 + 1)) := by
    have := bridge_ret n (fun r => (r : ℤ) ^ 2)
    rw [M2] at this
    exact_mod_cast this
  unfold pathMean
  rw [A0, A1, A2]
  have r1 := choose_rel (2 * n) n (by omega)
  have r2 := choose_rel (2 * n) (n + 1) (by omega)
  have r3 : ((2 * n).choose (n + 2 + 1) : ℚ) * ((n : ℚ) + 3) =
      ((2 * n).choose (n + 2) : ℚ) * ((n : ℚ) - 2) := by
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp [Nat.choose_eq_zero_of_lt]
    · have := choose_rel (2 * n) (n + 2) (by omega)
      push_cast at this ⊢
      linear_combination this
  push_cast at r1 r2 ⊢
  set c0 := ((2 * n).choose n : ℚ)
  set c1 := ((2 * n).choose (n + 1) : ℚ)
  set c2 := ((2 * n).choose (n + 2) : ℚ)
  set c3 := ((2 * n).choose (n + 2 + 1) : ℚ)
  have hc0 : 0 < c0 := by simp only [c0]; exact_mod_cast Nat.choose_pos (by omega)
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have e1 : c1 = c0 * n / (n + 1) := by field_simp; linear_combination r1
  have e2 : c2 = c1 * (n - 1) / (n + 2) := by field_simp; linear_combination r2
  have e3 : c3 = c2 * (n - 2) / (n + 3) := by field_simp; linear_combination r3
  rw [show (n : ℚ) + 1 + 1 = n + 2 by ring] at *
  rw [e3, e2, e1]
  have h0 : c0 - c0 * n / (n + 1) ≠ 0 := by
    rw [show c0 - c0 * n / (n + 1) = c0 / (n + 1) by field_simp; ring]; positivity
  field_simp
  ring

end MPAux

theorem returns_variance (n : ℕ) (hn : 1 ≤ n) :
    pathMean n (fun w => (returnCount n w : ℚ) ^ 2) -
        (pathMean n (fun w => (returnCount n w : ℚ))) ^ 2 =
      2 * (n : ℚ) * (n - 1) * (2 * n + 1) / ((n + 2) ^ 2 * (n + 3)) :=
  MPAux.ret_var n hn

namespace MPAux

/-! ### Variance of peaks -/

/-- Vandermonde's identity, written as a sum over `range`. -/
lemma VR (p q s : ℕ) :
    ∑ j ∈ range (s + 1), p.choose j * q.choose (s - j) = (p + q).choose s := by
  rw [Nat.add_choose_eq]
  exact (Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.choose i * q.choose j) s).symm

/-- Sort the walks by their number of peaks. -/
lemma fiber_pk (n : ℕ) (g : ℕ → ℚ) :
    ∑ w ∈ mountainPaths n, g (peakCount n w) =
      ∑ k ∈ range (2 * n + 1), (Np n k : ℚ) * g k := by
  rw [← sum_fiberwise_of_maps_to' (t := range (2 * n + 1)) (g := fun w => peakCount n w)
    (fun w _ => mem_range.2 (Nat.lt_succ_of_le ((card_filter_le _ _).trans (by simp))))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_const, nsmul_eq_mul]; rfl

/-- Replace each count by its Narayana value and drop the zero terms. -/
lemma peak_sum (m : ℕ) (f : ℕ → ℚ) :
    ((m : ℚ) + 1) * ∑ k ∈ range (2 * (m + 1) + 1), (Np (m + 1) k : ℚ) * f k =
      ∑ j ∈ range (m + 1), f (j + 1) * (((m + 1).choose (j + 1) : ℚ) * ((m + 1).choose j : ℚ)) := by
  rw [mul_sum, sum_range_succ', Np_zero]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  have key : ∀ j, ((m : ℚ) + 1) * ((Np (m + 1) (j + 1) : ℚ) * f (j + 1)) =
      f (j + 1) * (((m + 1).choose (j + 1) : ℚ) * ((m + 1).choose j : ℚ)) := by
    intro j
    have h' : ((m : ℚ) + 1) * (Np (m + 1) (j + 1) : ℚ) =
        ((m + 1).choose (j + 1) : ℚ) * ((m + 1).choose j : ℚ) := by
      exact_mod_cast pk_core m j
    rw [← h']; ring
  rw [sum_congr rfl fun j _ => key j]
  symm
  apply sum_subset (fun x hx => by rw [mem_range] at *; omega)
  intro j hj hj'
  rw [mem_range] at hj hj'
  rw [Nat.choose_eq_zero_of_lt (show m + 1 < j + 1 by omega)]; simp

lemma T0 (m : ℕ) :
    ∑ j ∈ range (m + 1), (m + 1).choose (j + 1) * (m + 1).choose j = (2 * m + 2).choose m := by
  rw [show 2 * m + 2 = (m + 1) + (m + 1) by ring, ← VR]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [Nat.choose_symm_of_eq_add (show m + 1 = (m - j) + (j + 1) by omega), mul_comm]

lemma T1 (m : ℕ) :
    ∑ j ∈ range (m + 1), (j + 1) * ((m + 1).choose (j + 1) * (m + 1).choose j) =
      (m + 1) * (2 * m + 1).choose m := by
  rw [show 2 * m + 1 = (m + 1) + m by ring, ← VR, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [Nat.choose_symm (show j ≤ m by omega)]
  have h1 := Nat.add_one_mul_choose_eq m j
  calc (j + 1) * ((m + 1).choose (j + 1) * (m + 1).choose j)
      = ((m + 1).choose (j + 1) * (j + 1)) * (m + 1).choose j := by ring
    _ = (m + 1) * ((m + 1).choose j * m.choose j) := by rw [← h1]; ring

lemma T2 (m : ℕ) :
    ∑ j ∈ range (m + 1), (j + 1) * j * ((m + 1).choose (j + 1) * (m + 1).choose j) =
      (m + 1) * m * (2 * m).choose m := by
  rcases m with _ | q
  · simp
  · have hV : ∑ i ∈ range (q + 1), q.choose i * (q + 1 + 1).choose (q + 1 - i) =
        (2 * (q + 1)).choose (q + 1) := by
      rw [show 2 * (q + 1) = q + (q + 1 + 1) by ring, ← VR q (q + 1 + 1) (q + 1)]
      conv_rhs => rw [sum_range_succ]
      rw [Nat.choose_eq_zero_of_lt (show q < q + 1 by omega), zero_mul, add_zero]
    rw [sum_range_succ', ← hV, mul_sum]
    simp only [mul_zero, zero_mul, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [Nat.choose_symm_of_eq_add (show q + 1 + 1 = (q + 1 - i) + (i + 1) by omega)]
    have h1 := Nat.add_one_mul_choose_eq (q + 1) (i + 1)
    have h2 := Nat.add_one_mul_choose_eq q i
    calc (i + 1 + 1) * (i + 1) * ((q + 1 + 1).choose (i + 1 + 1) * (q + 1 + 1).choose (i + 1))
        = ((q + 1 + 1).choose (i + 1 + 1) * (i + 1 + 1)) * (i + 1) *
            (q + 1 + 1).choose (i + 1) := by ring
      _ = (q + 1 + 1) * ((q + 1).choose (i + 1) * (i + 1)) * (q + 1 + 1).choose (i + 1) := by
          rw [← h1]; ring
      _ = (q + 1 + 1) * (q + 1) * (q.choose i * (q + 1 + 1).choose (i + 1)) := by
          rw [← h2]; ring

theorem pk_var (n : ℕ) (hn : 1 ≤ n) :
    pathMean n (fun w => (peakCount n w : ℚ) ^ 2) -
        (pathMean n (fun w => (peakCount n w : ℚ))) ^ 2 =
      ((n : ℚ) - 1) * (n + 1) / (4 * (2 * n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  have T0q : ∑ j ∈ range (m + 1), (((m + 1).choose (j + 1) : ℚ) * ((m + 1).choose j : ℚ)) =
      ((2 * m + 2).choose m : ℚ) := by exact_mod_cast T0 m
  have T1q : ∑ j ∈ range (m + 1), (((j : ℚ) + 1) * (((m + 1).choose (j + 1) : ℚ) *
      ((m + 1).choose j : ℚ))) = ((m : ℚ) + 1) * ((2 * m + 1).choose m : ℚ) := by
    exact_mod_cast T1 m
  have T2q : ∑ j ∈ range (m + 1), (((j : ℚ) + 1) * j * (((m + 1).choose (j + 1) : ℚ) *
      ((m + 1).choose j : ℚ))) = ((m : ℚ) + 1) * m * ((2 * m).choose m : ℚ) := by
    exact_mod_cast T2 m
  have S0 : ((mountainPaths (m + 1)).card : ℚ) = ((2 * m + 2).choose m : ℚ) / ((m : ℚ) + 1) := by
    have h := fiber_pk (m + 1) (fun _ => 1)
    simp only [sum_const, nsmul_eq_mul, mul_one] at h
    have hs := peak_sum m (fun _ => 1)
    simp only [mul_one, one_mul] at hs
    rw [eq_div_iff hm, mul_comm, h, hs]; exact T0q
  have S1 : ∑ w ∈ mountainPaths (m + 1), (peakCount (m + 1) w : ℚ) =
      ((2 * m + 1).choose m : ℚ) := by
    apply mul_left_cancel₀ hm
    rw [fiber_pk (m + 1) (fun k => (k : ℚ)), peak_sum m (fun k => (k : ℚ))]
    push_cast; exact T1q
  have S2 : ∑ w ∈ mountainPaths (m + 1), (peakCount (m + 1) w : ℚ) ^ 2 =
      (m : ℚ) * ((2 * m).choose m : ℚ) + ((2 * m + 1).choose m : ℚ) := by
    apply mul_left_cancel₀ hm
    rw [fiber_pk (m + 1) (fun k => (k : ℚ) ^ 2), peak_sum m (fun k => (k : ℚ) ^ 2)]
    push_cast
    have : ∑ j ∈ range (m + 1), (((j : ℚ) + 1) ^ 2 * (((m + 1).choose (j + 1) : ℚ) *
        ((m + 1).choose j : ℚ))) =
        ((m : ℚ) + 1) * m * ((2 * m).choose m : ℚ) + ((m : ℚ) + 1) * ((2 * m + 1).choose m : ℚ) := by
      rw [← T2q, ← T1q, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [this]; ring
  have rB : ((2 * m).choose m : ℚ) * (2 * m + 1) = ((2 * m + 1).choose m : ℚ) * (m + 1) := by
    have := Nat.choose_mul_succ_eq (2 * m) m
    rw [show 2 * m + 1 - m = m + 1 by omega] at this
    exact_mod_cast this
  have rP : ((2 * m + 1).choose m : ℚ) * (2 * m + 2) = ((2 * m + 2).choose m : ℚ) * (m + 2) := by
    have := Nat.choose_mul_succ_eq (2 * m + 1) m
    rw [show 2 * m + 1 + 1 - m = m + 2 by omega] at this
    exact_mod_cast this
  unfold pathMean
  rw [S0, S1, S2]
  set B := ((2 * m).choose m : ℚ)
  set P := ((2 * m + 1).choose m : ℚ)
  set Q := ((2 * m + 2).choose m : ℚ)
  have hB : 0 < B := by simp only [B]; exact_mod_cast Nat.choose_pos (by omega)
  have eP : P = B * (2 * m + 1) / (m + 1) := by field_simp; linear_combination -rB
  have eQ : Q = P * (2 * m + 2) / (m + 2) := by field_simp; linear_combination -rP
  rw [eQ, eP]
  push_cast
  rw [show 2 * ((m : ℚ) + 1) - 1 = 2 * m + 1 by ring]
  have h2 : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

end MPAux

theorem peaks_variance (n : ℕ) (hn : 1 ≤ n) :
    pathMean n (fun w => (peakCount n w : ℚ) ^ 2) -
        (pathMean n (fun w => (peakCount n w : ℚ))) ^ 2 =
      ((n : ℚ) - 1) * (n + 1) / (4 * (2 * n - 1)) :=
  MPAux.pk_var n hn
