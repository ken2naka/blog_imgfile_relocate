# -*- coding: utf-8 -*-
import os
# import pathlib
# import codecs
from bs4 import BeautifulSoup

# import urllib.request
# import urllib.error

# from socket import timeout
import re
import sys
import sqlite3
import argparse
# from logging import getLogger, StreamHandler, Filter, basicConfig, DEBUG
import logging
import io
from tqdm import tqdm
import inspect
import shutil

# type annotation
# from typing import Callable, Iterable, Union, Optional
from typing import List, Tuple  # , Optional, Set, Dict,
from typing import IO
from typing import Any, cast, Pattern, Union, Match, Optional, Iterator

# 以下の行が無いと git bash で実行した時、unicodeEncodeError となる。それを防止する。
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

G_VER_STR = '0.57'  # version number of this program

# このスクリプト本体のロガーを取得してログレベルを設定する
logger = logging.getLogger(__name__)

logf = False


# グローバル・データ
class Gd:
    img_dir: str = "img"
    db_name: str = "fc2.db"

    fo: Optional[IO[str]] = None
    out_file: str = "report_img_relocate.text"
    RE_SCRAPE_URL: List[str] = [] # ["http://xxx.blog.fc2.com", "https://xxx.blog.fc2.com"]
    RE_SCRAPE_FILE: str = 'must_recrape.text'

    err_count: int = 0
    warn_count: int = 0
    emp_count: int = 0  # 当該 url の記事が空だった件数
    ext_image_count: int = 0

    # 起動パラメータで設定されるフラグ
    move: bool = False
    copy: bool = False
    check: bool = False

    # 画像が含まれ、過去記事を参照している記事の id を指定すること。
    urls_no: List[int] = [120, 123]  # "-ndef" 指定時に使用される URL リスト。デバッグ用
    ndef: bool = False
    nlist: bool = False
    url_must_scrape: List[int] = []


class PyColor:
    BLACK = '\033[30m'
    RED = '\033[31m'
    GREEN = '\033[32m'
    YELLOW = '\033[33m'
    BLUE = '\033[34m'
    PURPLE = '\033[35m'
    CYAN = '\033[36m'
    WHITE = '\033[37m'
    END = '\033[0m'
    BOLD = '\038[1m'
    UNDERLINE = '\033[4m'
    INVISIBLE = '\033[08m'
    REVERSE = '\033[07m'


# 例外
class Param_error(Exception):
    # TODO : 未実装
    pass


# --------------------
# 不要なタグを削除、置換する。
# --------------------
def remove_tags(orig_str: str) ->str:
    from xml.sax.saxutils import unescape

    dest: str = orig_str.replace("<br/>", "\n")
    dest = dest.replace('<div class="entry_body">', "")
    dest = dest.replace(r"</div>", "")
    dest = dest.replace("[\t]", "")

    dest = unescape(dest)  # HTML エスケープ文字を通常の文字に変換

    # 初期の記事に何故か不要なタブや改行（xyzzy で '\r'（'^M' と表示されるもの））
    # が含まれている。それを除去
    dest = dest.replace("\r", "")
    dest = dest.replace("\t\t\t", "")
    return dest


# --------------------
#
# --------------------
def mk_paren_seqnum(dest_path: str) -> Tuple[str, int]:
    r""" ファイル名の重複チェック、変名処理。
    ファイル名が重複すれば、 (1),(2), ...(123) のようにカッコ付きの連番を付与したパス名を返す。
    Parameters
    ------
    dest_path :string
        パス（絶対 or 相対パス形式。ディレクトリ＋ファイル名）
        例： "d:\prog\my_work\clowing_prog\img\2018-11\abc.jpg"

    Returns
    ------
    ret_path : basestring
        重複時：括弧付きのパス。絶対パス形式。
        例1： r"d:\prog\my_work\clowing_prog\img\2018-11\abc(1).jpg"
              既に abc.jpg が存在する場合。

        例2： r"d:\prog\my_work\clowing_prog\img\2018-11\abc(3).jpg"
              既に abc.jpg, abc(1).jpg, abc(2).jpg が存在する場合。

        重複なし：そのままのパス（絶対パス）、 -1
              r"d:\prog\my_work\clowing_prog\img\2018-11\abc.jpg"

        エラー時： Param_error 割り込みを発生させる。

        :param dest_path:
        :type dest_path:
        :return:
        :rtype:
    """
    # ディレクトリの場合はエラー
    if os.path.isdir(dest_path):
        print("### Error! File path expected, but assiend directory({}, in {}".format(
            dest_path, sys._getframe().f_code.co_name), file=sys.stderr)
        raise Param_error("File path expect, but directory assignd.")

    dest_abs: str = os.path.abspath(dest_path)  # 絶対パスに。

    # 既に同名の画像ファイルが存在するか？
    if os.path.exists(dest_abs):
        # TODO : check-sum の比較もいずれ追加すること。
        # 既に存在する画像ファイルのサイズを得る。
        file_size = os.path.getsize(dest_abs)

        no = 1
        path_up_part, ext_name = os.path.splitext(dest_abs)
        cand_path = path_up_part + '(' + str(no) + ')' + ext_name
        while os.path.exists(cand_path):
            no += 1
            cand_path = path_up_part + '(' + str(no) + ')' + ext_name
            if (no > 99):
                print("### Error! too many number(>99 at {}".format(
                    sys._getframe().f_code.co_name), file=sys.stderr)
                raise Param_error("Too many image file that share common name.")

        return cand_path, file_size
    else:
        return dest_abs, -1  # 同名の画像ファイルが存在しない場合、file_size = -1


# --------------------
# 記事本文から画像ファイルのリンク部分を抽出。
# --------------------
def relocate_local_imagefiles() -> None:
    def base_name_of_url(url: str):
        re_pat = re.compile(r'([^/]+)$')
        m = re_pat.search(url)
        if m:
            return m.group()
        else:
            msg = "### Error! Illagel image source URL:{}".format(url)
            logger.error(msg)
            print(msg, file=sys.stderr)
            Gd.err_count += 1
            return url

    # 一見無駄のようだが、必要。
    def is_include(old_img_path: str, orig_list: list)->bool:
        if old_img_path in orig_list:
            return True
        else:
            return False

    def urlno_2_imgdir(url_no: int) -> str:
        num = int(url_no / 100)
        return '{:0=5}'.format(num)

    def date_2_imgdir(date_created: str) -> str:
        return date_created[:-3]

    # 記事中にリンクしている画像の URL を書き換える。
    #  a_url : 例 "https://blog-img-ramdom.fc2.com/n/e/w/xxx/20180916_book.jpg"
    #  return: 例 "https://my_blog.com/blog_article/img/<img_dir>/20180916_book.jpg"
    #  ここで <img_dir> は 5桁の数字。元の記事の int(url_no / 100) に相当。
    def trans_img_url(a_url: str, url_no: int) -> str:
        base_part = base_name_of_url(a_url)
        dir_str = urlno_2_imgdir(url_no)
        ret_str = "http://my_blog.com/blog_article/img/" + dir_str + "/" + base_part
        return ret_str

    # a_url の拡張子をチェックして、HTML （html, htm）の場合に True を返す。
    def is_html(a_url: str, url_no: int) -> bool:
        re_pat = re.compile(r'\.([^.]+)$')
        m = re_pat.search(a_url)
        if not m:
            msg = "### Error! at {}({}). string not match.".format(sys._getframe().f_code.co_name, a_url)
            logger.error(msg)
            print(msg, file=sys.stderr)
            Gd.err_count += 1
            return False

        ext_str = m.group(1)
        # print("{}(): m:{}".format(sys._getframe().f_code.co_name, ext_str))
        if ext_str.lower() in ["html", "htm"]:
            return True
        elif ext_str.lower() in ["jpg", "jpeg", "gif", "png", "svg"]:
            return False
        elif a_url.lower() in Gd.RE_SCRAPE_URL:
            # 空きスペース確保用の暫定記事に対応。
            Gd.url_must_scrape.append(url_no)
            return True

        re_pat2 = re.compile(r'html#comment\d+$')
        re_pat3 = re.compile(r'com/\?act=reply&tid=\d+$')
        m2 = re_pat2.search(ext_str.lower())
        m3 = re_pat3.search(ext_str.lower())
        if m2 or m3:
            return True
        else:
            msg = "### Warning! url_no: {} unexpected URL extension.{} : {}".format(url_no, ext_str, a_url)
            logger.warning(msg)
            print(msg, file=sys.stderr)
            Gd.warn_count += 1
            return False

    def move_image_files(body_str: str, url_no: int, date_create: str) -> None:
        def relocate_img(old_img_path: str, new_img_path: str, mv_list: list, img_type: str) -> None:
            if Gd.move:
                # TODO : 要確認
                # shutil.move(old_img_path, new_img_path, exist_ok = True)
                mv_list.append("{}: mv {} {}".format(img_type, old_img_path, new_img_path))
                msg = "@@@ shutil.move({}, {}, exist_ok = True)".format(old_img_path, new_img_path)
                logger.debug(msg)
                pass
            elif Gd.copy:
                # TODO : 要認後
                # shutil.copy2(old_img_path, new_img_path)
                mv_list.append("{}: cp {} {}".format(img_type, old_img_path, new_img_path))
                msg = "@@@ shutil.copy2({}, {})".format(old_img_path, new_img_path)
                logger.debug(msg)
                pass
            elif Gd.check:
                mv_list.append("{}: plan : {} --> {}".format(img_type, old_img_path, new_img_path))
                msg = "@@@ check... in {}: We will plan to move... {} --> {} ".format(sys._getframe().f_code.co_name, old_img_path, new_img_path)
                logger.debug(msg)
                pass
            else:
                msg = "### Non of (move, copy, check) specified. in {}".format(sys._getframe().f_code.co_name)
                logger.error(msg)
                msg = " old image path:{}, new image path:{}".format(old_img_path, new_img_path)
                logger.error(msg)
                Gd.err_count += 1

        msg = "\n\n{}() start...: url_no:{}".format(sys._getframe().f_code.co_name, url_no)
        logger.debug(msg)

        sp4 = BeautifulSoup(body_str, "lxml")

        # 注意：以下の二つのリストの初期化では mv_list = orig_list = [] としてはならない。同じリストとして扱われる。
        mv_list: List[str] = []
        orig_list: List[str] = []

        imgs = sp4.find_all("img", src=re.compile("^http"))
        # 埋め込まれた画像の抽出  <img ... src="http...."
        no = 0
        for img in imgs:
            no += 1
            msg = "\nimg no:{}, img:{}".format(no, img.__str__())
            logger.debug(msg)
            # print("name:{}".format(img.name))
            # print("src:{}".format(img['src']))

            re_pat = re.compile(r"^http.+fc2\.com")
            m = re_pat.match(img['src'])  # 先頭からマッチ。
            if not m:
                msg = "### Warning! EXTERNAL image link skipped.:{}".format(img['src'])
                logger.warning(msg)
                print(msg, file=sys.stderr)
                Gd.ext_image_count += 1
                continue

            # print("src-->basename:{}".format(base_name_of_url(img['src'])))
            old_img_path = "img/" + date_2_imgdir(date_create) + '/' + base_name_of_url(img['src'])
            new_img_path = "img/" + urlno_2_imgdir(url_no) + '/' + base_name_of_url(img['src'])

            if not os.path.exists(old_img_path):
                # 古いディレクトリ（img/2018-12/ など）に画像ファイルが存在しない場合。
                # 既に新しいディレクトリ（img/00124/ など）に格納されている筈。
                if not os.path.exists(new_img_path):
                    msg = "### Error! image file <img src=http...> not found! In: {}, url_no:{}, nor old_img_path:{} nither new_img_path:{}"\
                        .format(sys._getframe().f_code.co_name, url_no, old_img_path, new_img_path)
                    logger.error(msg)
                    print(msg, file=sys.stderr)
                    Gd.url_must_scrape.append(url_no)
                    Gd.err_count += 1
            else:
                # msg = "mv {} {}".format(old_img_path, new_img_path)
                # logger.debug(msg)
                orig_list.append(old_img_path)
                relocate_img(old_img_path, new_img_path, mv_list, "src ")

        # <a href=... でリンクされた記事と画像の抽出。
        # fc2.com 以外のリンク先は無視。
        hrefs = sp4.find_all(href=re.compile(r"fc2\.com"))
        no2 = 0
        for href in hrefs:
            href_str: str = href['href']
            href_str = href_str.rstrip()  # 末尾の空白除去

            # url の末尾に '/' がついている事例がある。
            # 　　具体例：a href="http://xxx.blog.fc2.com/img/20990403_CNTR.jpg/"
            # このような場合を考慮して末尾に '/' があれば、削除しておく。
            if href_str[-1:] == '/':
                href_str = href_str[:-1]

            msg = "\nhref no:{}, href:{}".format(no2, href)
            logger.debug(msg)
            msg = "href:{}".format(href_str)
            logger.debug(msg)

            if is_html(href_str, url_no):  # リンクしているのが html ファイル（＝過去記事）の場合
                # new_url = trans_article_url(href_str)
                pass
            else:  # リンクしているのが画像の場合
                old_img_path = "img/" + date_2_imgdir(date_create) + '/' + base_name_of_url(href_str)
                new_img_path = "img/" + urlno_2_imgdir(url_no) + '/' + base_name_of_url(href_str)

                # if old_img_path in orig_list:  # if ブロックの中で orig_list を変更するのはまずい？
                if is_include(old_img_path, orig_list):
                    # img で埋め込まれた画像が既にリストに含まれていればスキップ
                    msg = "*** regsterd. skip:{}".format(old_img_path)
                    logger.debug(msg)
                    pass
                else:
                    no2 += 1
                    if not os.path.exists(old_img_path):
                        # 古いディレクトリ（img/2018-12/ など）に画像ファイルが存在しない場合。
                        # 既に新しいディレクトリ（img/00124/ など）に格納されている筈。
                        if not os.path.exists(new_img_path):
                            msg = "### Error! image file <a href=...> not found! In: {}, url_no:{}, nor old_img_path:{} nither new_img_path:{}" \
                                .format(sys._getframe().f_code.co_name, url_no, old_img_path, new_img_path)
                            logger.error(msg)
                            print(msg, file=sys.stderr)
                            Gd.url_must_scrape.append(url_no)
                            Gd.err_count += 1
                    else:
                        msg = "mv {} {}".format(old_img_path, new_img_path)
                        logger.debug(msg)
                        orig_list.append(old_img_path)
                        relocate_img(old_img_path, new_img_path, mv_list, "href")

        if no == 0 and no2 == 0:
            # 埋め込まれている画像が無かった場合。
            msg = "\n\n*** url_no:{} no image file detected.***\n".format(url_no)
            logger.debug(msg)
            print(msg, file=Gd.fo)
        else:
            msg = "\n\n*** url_no:{} total {} image files moved. ***".format(url_no, no + no2)
            logger.debug(msg)
            print(msg, file=Gd.fo)
            n = 0
            for item in mv_list:
                n += 1
                msg = "{:>6}:{}".format(n, item)
                logger.debug(msg)
                print(msg, file=Gd.fo)

    # end of move_image_files()

    # -----------------------------------
    # ここから処理の開始
    # -----------------------------------
    if not os.path.exists(Gd.db_name):
        msg = "### Error! no db\n"
        logger.error(msg)
        print(msg, file=sys.stderr)
        Gd.err_count += 1
        return

    db = sqlite3.connect(Gd.db_name)
    cur = db.cursor()

    if Gd.ndef or Gd.nlist:
        # tqdm を使用する。そのためにレコード総数を予め求めておく。
        max_rec = len(Gd.urls_no)
    else:
        sql = "SELECT count(*) FROM fc2"
        cur.execute(sql)
        result = cur.fetchall()
        max_rec = result[0][0]
        msg = " in {} : total record count:{}".format(sys._getframe().f_code.co_name, max_rec)
        logger.debug(msg)

    pbar = tqdm(total=max_rec)  # 進捗バー

    sql = "SELECT id, url, title, date_create, category, body, comment, url_no FROM fc2 ORDER BY url_no"
    no = 0
    for row in cur.execute(sql):
        no += 1

        if Gd.ndef or Gd.nlist:
            if not (row[7] in Gd.urls_no):
                continue

        body_conv = remove_tags(row[5])

        move_image_files(body_conv, row[7], row[3])  # row[7]: url_no, row[3] : date_create
        pbar.update(1)

    pbar.close()
    db.close()


# --------------------
#  read_file_blog_url
#  "blog_url.text" を読み出して RE_SCRAPE_URL に設定する。
# --------------------
def read_file_blog_url() ->None:
    # RE_SCRAPE_URL
    url_text_file = "blog_url.text"

    for i, item in enumerate(Gd.RE_SCRAPE_URL):
        print("{}: <{}>".format(i, item))

    # TODO : 一気に readlines で読み込んでから list の各要素の改行を除去する方式を検討すること。

    lines: List[str] = []
    if os.path.exists(url_text_file):
        with open("blog_url.text", 'r') as fin:
            for s_line in fin:
                print(s_line)
                lines.append(s_line.rstrip())
    else:
        msg = "### Error! File ({}) not found.".format(url_text_file)
        print(msg, file=sys.stderr)
        sys.exit()

    for i, item in enumerate(lines):
        print("{}: <{}>".format(i, item))

    Gd.RE_SCRAPE_URL = lines

    for i, item in enumerate(Gd.RE_SCRAPE_URL):
        print("post {}: <{}>".format(i, item))


# --------------------
#  read_file_blog_url
#  "blog_url.text" を読み出して RE_SCRAPE_URL に設定する。
# --------------------
def read_file_blog_url2() ->None:
    # RE_SCRAPE_URL
    url_text_file = "blog_url.text"

    for i, item in enumerate(Gd.RE_SCRAPE_URL):
        print("{}: <{}>".format(i, item))

    #  一気に readlines で読み込んでから list の各要素の改行を除去。
    lines: List[str] = []
    if os.path.exists(url_text_file):
        with open("blog_url.text", 'r') as fin:
            lines = fin.readlines()
    else:
        msg = "### Error! File ({}) not found.".format(url_text_file)
        print(msg, file=sys.stderr)
        sys.exit()

    Gd.RE_SCRAPE_URL = map(lambda x: x.rstrip(), lines)

    for i, item in enumerate(Gd.RE_SCRAPE_URL):
        print("post {}: <{}>".format(i, item))


# --------------------
# コマンドライン引数の処理
# --------------------
def get_args():
    parser = argparse.ArgumentParser()

    # 必須パラメータ
    parser.add_argument("mode", choices=['check', 'copy'], help="select FILE COPY or CHECK ONLY(not copy)")

    # オプション・パラメータ
    parser.add_argument("-n", "--nlist", type=int, metavar="<url-num>",
                        nargs='*', help="crowling indivisial URL-No. (ex. -n 100 101 200)")
    parser.add_argument("-ndef", action="store_true",
                        help="use DEFAULT-LIST of URL-No. (for DEBUG)")

    parser.add_argument("-func_test", type=int, metavar="<test_no>",
                        help="test specified function. (for DEBUG)")
    parser.add_argument("-version", "--V", action="version",
                        version='%(prog)s ' + G_VER_STR)

    args = parser.parse_args()

    return args


# --------------------
if __name__ == "__main__":

    log_file = "logger.log"

    # 過去のログファイルを削除
    if os.path.exists(log_file):
        os.remove(log_file)

    if os.path.exists(Gd.RE_SCRAPE_FILE):
        os.remove(Gd.RE_SCRAPE_FILE)

    logger.setLevel(logging.WARNING)
    # logger.setLevel(logging.DEBUG)

    fh = logging.FileHandler(log_file, encoding='utf-8')
    logger.addHandler(fh)
    formatter = logging.Formatter(
        '%(asctime)s:%(funcName)s:%(lineno)d:%(levelname)s:%(message)s')
    fh.setFormatter(formatter)

    # ログのコンソール出力の設定
    """
    sh = logging.StreamHandler()
    logger.addHandler(sh)
    sh.setFormatter(formatter)
    """

    logger.debug("Logging start.")

    args = get_args()

    if 1:
        logger.debug("args.cmode={}".format(args.mode))
        logger.debug("args.nlist={}".format(args.nlist))
        logger.debug("args.ndef={}".format(args.ndef))
        logger.debug("args.func_test:{}".format(args.func_test))

    # 要約レポート・ファイル
    if os.path.exists(Gd.out_file):
        os.remove(Gd.out_file)
    Gd.fo = open(Gd.out_file, mode="a", encoding="utf-8")

    # "-ndef" が指定された。URL-no としてデフォルトのリストが指定された場合。
    # TODO : 要確認
    if args.ndef:
        Gd.ndef = True

    # "-n  1 2 100 200" が指定された。URL-no を戸別指定
    # TODO : 要確認
    if (args.nlist is not None) and (len(args.nlist) >= 1):
        Gd.nlist = True
        Gd.urls_no = args.nlist.copy()

    # "-check" が指定された。
    if args.mode == 'check':
        Gd.check = True
        relocate_local_imagefiles()
    elif args.mode == 'copy':
        Gd.copy = True
        relocate_local_imagefiles()
    else:
        print("### Error! Illagel mode argument:{}".format(args.mode))
        sys.exit()

    # 作成中の関数の個別テスト
    if args.func_test == 1:
        read_file_blog_url()
    elif args.func_test == 2:
        read_file_blog_url2()
    elif args.func_test == 3:
        pass
    elif args.func_test == 4:
        pass

    logger.debug("end fo logging.")
    Gd.fo.close()

    print("Total Error count:{}".format(Gd.err_count))
    print("Total Warning count:{}".format(Gd.warn_count))
    print("Total Empty count:{}".format(Gd.emp_count))
    print("Total External image link count:{}".format(Gd.ext_image_count))

    if len(Gd.url_must_scrape) > 0:
        with open(Gd.RE_SCRAPE_FILE, 'w', encoding="utf-8") as fo:
            print("URL must be recraped:", end="")
            for item in Gd.url_must_scrape:
                print(" {}".format(item), end="")
                print("{}".format(item), file=fo)
        print("\n  Total count:{}  (listed file:{})".format(len(Gd.url_must_scrape), Gd.RE_SCRAPE_FILE))
