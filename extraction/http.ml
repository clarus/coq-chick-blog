let requests_push_request =
  Lwt_react.E.create ()

let requests : string React.event =
  fst requests_push_request

let push (path : string) : unit =
  (snd requests_push_request) path

let callback (connection : Cohttp_lwt_unix.Server.conn) (request : Cohttp.Request.t)
  (body : Cohttp_lwt_body.t) : (Cohttp.Response.t * Cohttp_lwt_body.t) Lwt.t =
  let uri = Cohttp.Request.uri request in
  match Uri.path uri with
  | "/" -> Cohttp_lwt_unix.Server.respond_string `OK "index" ()
  | path -> Cohttp_lwt_unix.Server.respond_string `Not_found (path ^ " not found") ()

let start_server (port : int) : unit Lwt.t =
  let config = Cohttp_lwt_unix.Server.make callback () in
  Lwt.bind (Lwt_io.printlf "HTTP server starting on port %d." port) (fun _ ->
  Cohttp_lwt_unix.Server.create ~mode:(`TCP (`Port port)) config)
