import Lean
import Mathlib.Tactic

set_option maxHeartbeats 10000000

/-
PROVIDED SOLUTION
Induction on l. Base case trivial. Inductive case: split on whether hd = ch, use that set! preserves size and that get! after set! at same index gives new value and at different index gives old value. Char.toNat is injective (Char.ext).
-/
theorem foldl_freq_count_list (l : List Char) (ch : Char) (hch : ch.toNat < 128)
    (acc : Array Nat) (hacc : acc.size = 128) :
    (l.foldl (fun (acc : Array Nat) (c : Char) =>
      let idx := c.toNat
      if idx < acc.size then acc.set! idx (acc[idx]! + 1) else acc) acc)[ch.toNat]!
    = acc[ch.toNat]! + l.countP (fun x => decide (x = ch)) := by
  induction' l using List.reverseRecOn with l ih;
  · rfl;
  · by_cases h : ih.toNat = ch.toNat <;> simp_all +decide [ List.countP_append ];
    · split_ifs <;> simp_all +decide [ Char.ext_iff ];
      · ring;
      · exact ‹¬ih.val = ch.val› ( by rw [ ← Char.ofNat_toNat ih, ← Char.ofNat_toNat ch, h ] );
      · rename_i h₁ h₂ h₃;
        contrapose! h₂;
        induction' l using List.reverseRecOn with l ih;
        · aesop;
        · grind;
    · grind