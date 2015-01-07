open Cohttp_lwt_unix

let callback (connection : Server.conn) (request : Cohttp.Request.t)
  (body : Cohttp_lwt_body.t) : (Cohttp.Response.t * Cohttp_lwt_body.t) Lwt.t =
  Server.respond_string `OK "Hello" ()

let main () =
  let config = Server.make callback () in
  let server : unit Lwt.t = Server.create ~mode:(`TCP (`Port 8001)) config in
  Lwt_main.run server

;;main ()
