import Std.Tactic.BVDecide

#check Float
#check Float32
#check UInt64

structure Double where
  ofBitVec ::
  toBitVec : BitVec 64

namespace Double

def sign : Double → Bool | ⟨x⟩ => x.msb
def exponent : Double → BitVec 11 | ⟨x⟩ => x.extractLsb' 52 11
def fraction : Double → BitVec 52 | ⟨x⟩ => x.truncate 52
theorem bitVec_def : {d : Double} → BitVec.ofBool d.sign ++ d.exponent ++ d.fraction = d.toBitVec
  | ⟨x⟩ => show BitVec.ofBool x.msb ++ x.extractLsb' 52 11 ++ x.truncate 52 = x by grind

example {x : BitVec 64} : BitVec.ofBool x.msb ++ x.extractLsb' 52 11 ++ x.truncate 52 = x :=
  by bv_decide
#check BitVec.msb_ofBool
#check BitVec.msb_append
#check BitVec.msb_extractLsb'
#check BitVec.extractLsb'_eq_self
#check BitVec.setWidth_append_of_eq
#check BitVec.setWidth_eq_append_extractLsb'
#check BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
#check BitVec.ofBool_append
#check BitVec.cons_append
#check BitVec.cons_msb_setWidth
example {x : BitVec 64} : BitVec.ofBool x.msb ++ x.extractLsb' 52 11 ++ x.truncate 52 = x :=
  have : x.truncate 52 = x.extractLsb' 0 52 := rfl
  have : x.extractLsb' 0 64 = x := x.extractLsb'_eq_self
  have : (x.extractLsb' 52 12).msb = x.msb := x.msb_extractLsb'
  have : BitVec.ofBool x.msb = x.extractLsb' 63 1 := by grind
  calc BitVec.ofBool x.msb ++ x.extractLsb' 52 11 ++ x.truncate 52
    _ = BitVec.cons x.msb (x.extractLsb' 52 11 ++ x.extractLsb' 0 52) := BitVec.cons_append ..
    _ = BitVec.cons x.msb (x.extractLsb' 0 63)
    := congrArg _ (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl)
    _ = x := x.cons_msb_setWidth

end Double
