:- module fjogg.
%==============================================================================%
% Native Mercury implementation of a reader for the ogg media container.
%
% The normal way to decode an ogg-contained media file is to call repeatedly
% call read_page until eof is returned. For each page, call packet_out, and if
% the next call to packet_out succeeds, immediately use the codec of your choice
% on the data. If packet_crosses_page succeeds, then you need to add the output
% of packet_out from the next page to the current output. Otherwise, decode as
% normal.
%
% Note that when a packet crosses a page boundary, you must read from the input
% stream before calling read_page again.
%
% Feel free to calculate the CRC32 of the page's packets as you decode them.
:- interface.
%==============================================================================%

:- use_module io.

%------------------------------------------------------------------------------%

% Shorthand
:- type input == io.binary_input_stream.

:- type page.

%------------------------------------------------------------------------------%

:- pred read_page(input, io.result(page), io.io, io.io).
:- mode read_page(in, out, di, uo) is det.

% Gets a packet from the page. Succeeds if there is another packet on the page,
% fails if the page is done.
% On success, indicates the amount of data to read from the file.
% packet_out(!Page, Size)
:- pred packet_out(page, page, int).
:- mode packet_out(in, out, uo) is semidet.

% Succeeds if the last packet from packet_out is continued on the next page.
:- pred packet_crosses_page(page::in) is semidet.

:- pred last_packet(page::in) is semidet.

%------------------------------------------------------------------------------%

% These functions are not vitally necessary, but can be used to check for ogg
% consistency. The CRC32 is particularly useful for this per page, and the page
% number is very useful for the entire file. The BOS/EOS flags are not really
% needed, the information is redundant for an entire ogg stream, and more useful
% if for some reason you are jumping in to the stream in the middle.

% This should be a strictly sequentially increasing number for each page in the
% stream.
:- func page_number(page) = int.

:- func stream_serial(page) = int.

% CRC for the entire page of packet data, not just a single packet.
:- func crc32(page) = int.

% Succeeds if a logical stream starts on this page.
:- pred bos(page::in) is semidet.

% Succeeds if a logical stream ends on this page.
:- pred eos(page::in) is semidet.

% Succeeds if the first packet is continuing the final packet on the last page.
:- pred continuation(page::in) is semidet.

%==============================================================================%
:- implementation.
%==============================================================================%

:- import_module int.
:- import_module list.

:- use_module stream.
:- use_module string.

%------------------------------------------------------------------------------%

:- type segs == list.list(int).
:- type continues ---> continues ; ends.
:- type page ---> page(
    flags::int, page_num::int, stream_num::int, crc::int, num_segs::int, segments::segs, continue::continues).

%------------------------------------------------------------------------------%

packet_crosses_page(Page) :- Page ^ continue = continues.

%------------------------------------------------------------------------------%

page_number(Page) = Page ^ page_num.

%------------------------------------------------------------------------------%

stream_serial(Page) = Page ^ stream_num.

%------------------------------------------------------------------------------%

crc32(Page) = Page ^ crc.

%------------------------------------------------------------------------------%

bos(Page) :- Page ^ flags /\ (1 << 1) = (1 << 1).

%------------------------------------------------------------------------------%

eos(Page) :- Page ^ flags /\ (1 << 2) = (1 << 2).

%------------------------------------------------------------------------------%

continuation(Page) :- Page ^ flags /\ 1 = 1.

%------------------------------------------------------------------------------%

last_packet(Page) :- Page ^ segments = [].

%------------------------------------------------------------------------------%

%  Reader bodies. In all likelihood only version 0 will ever exist.
:- pred read_page_v0(input, io.result(page), io.io, io.io).
:- mode read_page_v0(in, out, di, uo) is det.

%------------------------------------------------------------------------------%

:- func eof(string) = io.error.
eof(Where) = io.make_io_error(string.append("Unexpected EOF at ", Where)).

%------------------------------------------------------------------------------%

% Utility to read in a 32-bit integer, from LSB to MSB.
:- pred read_int32(input, io.result(int), io.io, io.io).
:- mode read_int32(in, out, di, uo) is det.

read_int32(In, Res, !IO) :-
    io.read_byte(In, Res0, !IO),
    io.read_byte(In, Res1, !IO),
    io.read_byte(In, Res2, !IO),
    io.read_byte(In, Res3, !IO),
    (
        Res0 = io.eof, Res = io.eof
    ;
        Res0 = io.error(Err), Res = io.error(Err)
    ;
        Res0 = io.ok(Int0),
        (
            Res1 = io.eof, Res = io.eof
        ;
            Res1 = io.error(Err), Res = io.error(Err)
        ;
            Res1 = io.ok(Int1),
            (
                Res2 = io.eof, Res = io.eof
            ;
                Res2 = io.error(Err), Res = io.error(Err)
            ;
                Res2 = io.ok(Int2),
                (
                    Res3 = io.eof, Res = io.eof
                ;
                    Res3 = io.error(Err), Res = io.error(Err)
                ;
                    Res3 = io.ok(Int3),
                    Res = io.ok(Int),
                    Int = Int0 \/ ( Int1 << 8 ) \/ (Int2 << 16) \/ (Int3 << 24)
                )
            )
        )
    ).

%------------------------------------------------------------------------------%

:- pred match(input, list.list(int), string, io.res, io.io, io.io).
:- mode match(in, in, in, out, di, uo) is det.

match(_, [], _, io.ok, !IO).
match(In, [Byte|List], Msg, Res, !IO) :-
    io.read_byte(In, ByteResult, !IO),
    (
        ByteResult = io.eof,
        Res = io.error(io.make_io_error(Msg))
    ;
        ByteResult = io.error(Err),
        Res = io.error(Err)
    ;
        ByteResult = io.ok(InByte),
        ( InByte = Byte ->
            match(In, List, Msg, Res, !IO)
        ;
            Res = io.error(io.make_io_error(Msg))
        )
    ).

%------------------------------------------------------------------------------%

% read_segs(Input, MaxSegs, CurSeg, LastByte, CurSegTotals, SegTotalsOut, Continues, !IO)
:- pred read_segs(input, int, int, int, segs, io.res(segs), continues, io.io, io.io).
:- mode read_segs(in, in, in, in, in, out, uo, di, uo) is det.

:- pred unique_append(list(int), int, list(int)).
:- mode unique_append(di, in, uo) is det.
:- mode unique_append(in, in, out) is det.

unique_append(InList, InInt, OutList) :-
    list.append(InList, [InInt+0|[]], OutList).

read_segs(In, MaxSegs, CurSeg, LastByte, CurSegTotals, SegTotalsOut, Continues, !IO) :-
    ( MaxSegs = 0 ->
        ( LastByte = 255 ->
            Continues = continues
        ;
            Continues = ends
        ),
        SegTotalsOut = io.ok(SegTotals),
        ( CurSeg = 0 ->
            % Uhhh ?
            SegTotals = CurSegTotals
        ;
            list.append(CurSegTotals, [CurSeg+0|[]], SegTotals)
        )
    ;  
        io.read_byte(In, ByteRes, !IO),
        (
            % This is kind of OK. You could imagine a final empty page.
            % Really, we should check if this entire page is empty and report an
            % error otherwise, but for now, just swallow the weirdness. If the
            % page was non-zero, an eof error would occur trying to read the data
            % anyway.
            ByteRes = io.eof,
            unique_append(CurSegTotals, CurSeg, SegTotals),
            SegTotalsOut = io.ok(SegTotals),
            ( LastByte = 255 ->
                Continues = continues
            ;
                Continues = ends
            )
        ;
            ByteRes = io.error(Err), SegTotalsOut = io.error(Err),
            Continues = ends % Hmm, seems this ought to be stuck in the result.
        ;
            ByteRes = io.ok(Byte),
            ( Byte = 255 ->
                read_segs(In, MaxSegs-1, CurSeg+Byte, Byte, CurSegTotals, SegTotalsOut, Continues, !IO)
            ;
                unique_append(CurSegTotals, CurSeg+Byte, SegTotals),
                read_segs(In, MaxSegs-1, 0, Byte, SegTotals, SegTotalsOut, Continues, !IO)               
            )
        )
    ).

%------------------------------------------------------------------------------%

:- func ogg_byte_sig = list.list(int).
ogg_byte_sig = [0x4F|[0x67|[0x67|[0x53|[]]]]].

%------------------------------------------------------------------------------%

read_page(In, Res, !IO) :-
    % Read signature
    match(In, ogg_byte_sig, "Invalid Signature", SigRes, !IO),
    (
        SigRes = io.error(Err), Res = io.error(Err)
    ;
        SigRes = io.ok,
        io.read_byte(In, VerRes, !IO),
        ( % Match the version
            VerRes = io.eof,
            Res = io.error(eof("page version"))
        ;
            VerRes = io.error(Err), Res = io.error(Err)
        ;
            VerRes = io.ok(Ver),
            ( Ver = 0 ->
                read_page_v0(In, Res, !IO)
            ;
                Res = io.error(io.make_io_error(ErrMsg)),
                ErrMsg = string.append("Unknown version ", string.from_int(Ver))
            )
        )
    ).

%------------------------------------------------------------------------------%

read_page_v0(In, Res, !IO) :-
    io.read_byte(In, FlagsRes, !IO),
    (
        FlagsRes = io.eof, Res = io.error(eof("page flags"))
    ;
        FlagsRes = io.error(Err), Res = io.error(Err)
    ;
        FlagsRes = io.ok(Flags),
        stream.seek(In, stream.cur, 8, !IO), % Skip granule position.
        read_int32(In, StreamNumRes, !IO),
        (
            StreamNumRes = io.eof, Res = io.error(eof("stream serial number"))
        ;
            StreamNumRes = io.error(Err), Res = io.error(Err)
        ;
            StreamNumRes = io.ok(StreamNum),
            read_int32(In, PageNumRes, !IO),
            (
                PageNumRes = io.eof, Res = io.error(eof("page serial number"))
            ;
                PageNumRes = io.error(Err), Res = io.error(Err)
            ;
                PageNumRes = io.ok(PageNum),
                read_int32(In, CRCRes, !IO),
                (
                    CRCRes = io.eof, Res = io.error(eof("CRC"))
                ;
                    CRCRes = io.error(Err), Res = io.error(Err)
                ;
                    CRCRes = io.ok(CRC),
                    io.read_byte(In, NumSegmentsResult, !IO),
                    (
                        NumSegmentsResult = io.eof,
                        Res = io.error(eof("number of segments"))
                    ;
                        NumSegmentsResult = io.error(Err), Res = io.error(Err)
                    ;
                        NumSegmentsResult = io.ok(NumSegments),
                        read_segs(In, NumSegments, 0, 0, [], SegRes, C, !IO),
                        (
                            SegRes = io.error(Err), Res = io.error(Err)
                        ;
                            SegRes = io.ok(Segs),
                            Res = io.ok(Page),
                            Page = page(Flags, PageNum, StreamNum, CRC, NumSegments, Segs, C)
                        )
                    )
                )
            )
        )
    ).

%------------------------------------------------------------------------------%

packet_out(!Page, 0+Size) :-
    !.Page ^ segments = [Size|List],
    (!Page ^ segments := List).
