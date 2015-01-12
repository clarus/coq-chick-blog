let requests_push_request =
  Lwt_react.E.create ()

let requests : string React.event =
  fst requests_push_request

let push (path : string) : unit =
  (snd requests_push_request) path
