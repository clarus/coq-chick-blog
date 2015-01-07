open Cohttp_lwt_unix

let callback (connection : Server.conn) (request : Cohttp.Request.t)
  (body : Cohttp_lwt_body.t) : (Cohttp.Response.t * Cohttp_lwt_body.t) Lwt.t =
  let uri = Cohttp.Request.uri request in
  match Uri.path uri with
  | "/" -> Server.respond_string `OK "index" ()
  | path -> Server.respond_string `Not_found (path ^ " not found") ()

let main () =
  let config = Server.make callback () in
  let server : unit Lwt.t = Server.create ~mode:(`TCP (`Port 8001)) config in
  Lwt_main.run server

;;main ()
