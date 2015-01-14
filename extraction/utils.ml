open Big_int

let list_files (directory : string) : string list option Lwt.t =
  Lwt.catch (fun _ ->
    let file_names = Lwt_unix.files_of_directory directory in
    Lwt.bind (Lwt_stream.to_list file_names) (fun file_names ->
    Lwt.return @@ Some file_names))
    (fun _ -> Lwt.return None)

let list_posts () : ((string * big_int) * big_int) list option Lwt.t =
  Lwt.catch (fun _ ->
    let file_names = Lwt_unix.files_of_directory "posts" in
    Lwt.bind (Lwt_stream.to_list file_names) (fun file_names ->
    let headers = file_names |> List.map (fun file_name ->
      if Str.string_match (Str.regexp "^\\([0-9][0-9][0-9][0-9]\\)-\\([0-9][0-9]\\)-\\([0-9][0-9]\\) *\\(.*\\)\\.md$") file_name 0 then
        let year = big_int_of_string @@ Str.matched_group 0 file_name in
        let month = big_int_of_string @@ Str.matched_group 1 file_name in
        let day = big_int_of_string @@ Str.matched_group 2 file_name in
        let title = Str.matched_group 3 file_name in
        (* Some ((((file_name, year), month), day), title) *)
        Some ((file_name, year), month)
      else
        None) in
    let headers = List.fold_left (fun headers header ->
      match header with
      | None -> headers
      | Some header -> header :: headers)
      [] headers in
    Lwt.return @@ Some headers))
    (fun _ -> Lwt.return None)
