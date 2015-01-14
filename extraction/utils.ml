open Big_int

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

let read_file (file_name : string) : string option Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_io.open_file Lwt_io.Input file_name) (fun channel ->
    Lwt.bind (Lwt_io.read channel) (fun content ->
    Lwt.bind (Lwt_io.close channel) (fun _ ->
    Lwt.return @@ Some content))))
    (fun _ -> Lwt.return None)

let update_file (file_name : string) (content : string) : bool Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_io.open_file Lwt_io.Output file_name) (fun channel ->
    Lwt.bind (Lwt_io.write channel content) (fun content ->
    Lwt.bind (Lwt_io.close channel) (fun _ ->
    Lwt.return true))))
    (fun _ -> Lwt.return false)

let list_files (directory : string) : string list option Lwt.t =
  Lwt.catch (fun _ ->
    let file_names = Lwt_unix.files_of_directory directory in
    Lwt.bind (Lwt_stream.to_list file_names) (fun file_names ->
    Lwt.return @@ Some file_names))
    (fun _ -> Lwt.return None)

let start_server
  (handler : string list -> (string * string list) list -> (string * string) list ->
    ((string * (string * string) list) * string) Lwt.t)
  (port : int) : unit Lwt.t =
  let callback (connection : Cohttp_lwt_unix.Server.conn)
    (request : Cohttp.Request.t) (body : Cohttp_lwt_body.t)
    : (Cohttp.Response.t * Cohttp_lwt_body.t) Lwt.t =
    let uri = Cohttp.Request.uri request in
    let path = Str.split (Str.regexp_string "/") @@ Uri.path uri in
    let args = Uri.query uri in
    let cookies = Cohttp.Request.headers request
      |> Cohttp.Cookie.Cookie_hdr.extract in
    Lwt.bind (handler path args cookies) (fun ((mime_type, cookies), content) ->
    let cookies = cookies |> List.map (fun cookie ->
      Cohttp.Cookie.Set_cookie_hdr.make cookie
      |> Cohttp.Cookie.Set_cookie_hdr.serialize) in
    let headers = Cohttp.Header.of_list
      (("content-type", mime_type) :: cookies) in
    (Cohttp_lwt_unix.Server.respond_string ~headers:headers) `OK content ()) in
  let config = Cohttp_lwt_unix.Server.make callback () in
  Lwt.bind (Lwt_io.printlf "HTTP server starting on port %d." port) (fun _ ->
  Cohttp_lwt_unix.Server.create ~mode:(`TCP (`Port port)) config)
