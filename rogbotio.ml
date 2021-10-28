(* $Id: rogbotio.ml,v 1.5 2015/04/09 15:14:21 deraugla Exp $ *)

open Printf;

value string_create = Bytes.create;
value string_set = Bytes.set;

value is_socket_file name =
  let stats = Unix.lstat name in
  stats.Unix.st_kind = Unix.S_SOCK
;

value socket str = do {
  let addr =
    try Unix.ADDR_INET Unix.inet_addr_any (int_of_string str) with
    [ Failure _ -> do {
        if Sys.file_exists str then
          if is_socket_file str then Unix.unlink str
          else failwith (sprintf "error: file \'%s\' exists." str)
        else ();
        Unix.ADDR_UNIX str
      } ]
  in
  let s = Unix.socket (Unix.domain_of_sockaddr addr) Unix.SOCK_STREAM 0 in
  try do {
    Unix.setsockopt s Unix.SO_REUSEADDR True;
    Unix.bind s addr;
    Unix.listen s 1;
  }
  with e -> do {
    Unix.close s;
    raise e
  };
  eprintf "Waiting for socket connection...\n";
  flush stderr;
  let (s2, addr) = Unix.accept s in
  Unix.close s;
  s2
};

value rogbot_magic = "RGBT0001";

value getchar nrow ncol s = do {
  let txt = sprintf "%s\n" rogbot_magic in
  let txt = Bytes.of_string txt in
  let _ : int = Unix.write s txt 0 (Bytes.length txt) in
  let txt = sprintf "%d\n" nrow in
  let txt = Bytes.of_string txt in
  let _ : int = Unix.write s txt 0 (Bytes.length txt) in
  let txt = sprintf "%d\n" ncol in
  let txt = Bytes.of_string txt in
  let _ : int = Unix.write s txt 0 (Bytes.length txt) in
  let line = string_create ncol in
  for row = 0 to nrow - 1 do {
    for col = 0 to ncol - 1 do {
      string_set line col (Curses.mvinch row col);
    };
    let txt = sprintf "%s\n" (Bytes.to_string line) in
  let txt = Bytes.of_string txt in
    let _ : int = Unix.write s txt 0 (Bytes.length txt) in
    ()
  };
  let b = Bytes.of_string " " in
  let _ : int = Unix.read s b 0 1 in
  Bytes.get b 0
};

