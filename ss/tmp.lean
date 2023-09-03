variables {α : Type} [add_group α]
variables (a b c : α)
variable h : a - b = a - c

theorem example : b = c :=
begin
  apply sub_left_cancel h
end
