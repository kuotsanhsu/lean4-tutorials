import Std.Time.Date.Unit.Year

structure Book where
  identifier : String
  author : Array String
  editor : Array String
  title : String
  series : String
  volume : Nat
  year : Std.Time.Year.Offset
  publisher : String
