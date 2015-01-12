let requests_push_request =
  Lwt_react.E.create ()

let requests : string React.event =
  fst requests_push_request

let push (path : string) : unit =
  (snd requests_push_request) path

let callback (handler : string -> string Lwt.t)
  (connection : Cohttp_lwt_unix.Server.conn) (request : Cohttp.Request.t)
  (body : Cohttp_lwt_body.t) : (Cohttp.Response.t * Cohttp_lwt_body.t) Lwt.t =
  let path = Uri.path @@ Cohttp.Request.uri request in
  Lwt.bind (handler path) (fun response ->
  Cohttp_lwt_unix.Server.respond_string `OK response ())

let start_server (handler : string -> string Lwt.t) (port : int) : unit Lwt.t =
  let config = Cohttp_lwt_unix.Server.make (callback handler) () in
  Lwt.bind (Lwt_io.printlf "HTTP server starting on port %d." port) (fun _ ->
  Cohttp_lwt_unix.Server.create ~mode:(`TCP (`Port port)) config)
