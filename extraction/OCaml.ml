module String = struct
  let to_lstring s =
    let rec aux l i =
      if i = -1 then
        l
      else
        aux (s.[i] :: l) (i - 1) in
    aux [] (String.length s - 1)

  let of_lstring s =
    let length = List.length s in
    let buffer = String.create length in
    List.iteri (fun i c -> String.set buffer i c) s;
    buffer
end
