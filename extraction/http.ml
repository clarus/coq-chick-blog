let requests_push_request =
  Lwt_react.E.create ()

let requests : string React.event =
  fst requests_push_request

let push (path : string) : unit =
  (snd requests_push_request) path

let start_server
  (handler : string list -> (string * string list) list ->
    (string * string) Lwt.t)
  (port : int) : unit Lwt.t =
  let callback (connection : Cohttp_lwt_unix.Server.conn)
    (request : Cohttp.Request.t) (body : Cohttp_lwt_body.t)
    : (Cohttp.Response.t * Cohttp_lwt_body.t) Lwt.t =
    let uri = Cohttp.Request.uri request in
    let path = Str.split (Str.regexp_string "/") @@ Uri.path uri in
    let args = Uri.query uri in
    Lwt.bind (handler path args) (fun (mime_type, content) ->
    let headers = Cohttp.Header.init_with "content-type" mime_type in
    (Cohttp_lwt_unix.Server.respond_string ~headers:headers) `OK content ()) in
  let config = Cohttp_lwt_unix.Server.make callback () in
  Lwt.bind (Lwt_io.printlf "HTTP server starting on port %d." port) (fun _ ->
  Cohttp_lwt_unix.Server.create ~mode:(`TCP (`Port port)) config)
