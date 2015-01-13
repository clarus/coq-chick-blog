module StringMap = Map.Make(String)

let users : (string * string) StringMap.t ref =
  ref StringMap.empty

let users_get () : (string * (string * string)) list =
  StringMap.fold (fun login value l -> (login, value) :: l) !users []

let users_set (new_users : (string * (string * string)) list) : unit =
  users := List.fold_left (fun m (login, value) -> StringMap.add login value m)
    StringMap.empty new_users
