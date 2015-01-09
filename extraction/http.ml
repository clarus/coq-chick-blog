let requests, push_request =
  Lwt_react.E.create ()

let push (path : string) : unit =
  push_request path
