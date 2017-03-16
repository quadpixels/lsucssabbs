# -*- coding: utf-8 -*-
# lsu cssa mailing list -----> forum post converter
# 2016-02-15
# 2016-02-20: Ate too much Beignet Fingers!!
# 这个东西需求好像都不明确，所以只好尽快弄点能Work的东西出来了。
# 2016-03-01: Handle emoticons U+0001F62C
# 2016-03-02: 修正了隐去邮箱地址用的正则表达式，不然匹配得太多，把整封信都砍掉了。
# 2016-03-02: 把企鹅隐去、把微信隐去、Emoticon U+0001F64F、邮件标题也需要经过sql转换（主要是单引号必须变成连续两个单引号）
# 2016-03-06: U+0001F604 【:D】
# 需要完成的功能：
#   ＊ 检测两封一模一样的邮件，如果一样的话就要在导入的时候无视。
#   ＊ pickle化已经导入了的邮件
# 2016-03-08: 把时区也一同解析出来
# 2016-04-11: 对于反斜杠，要escape一下，不然就会被吞了。
# 2016-05-10: Todo List：想需要把附件中的图片解出来
# 2016-05-16: Working on 把图片解出来 ... Done，都存在了{邮件名称}/xxx.{jpg|png...}之下。
# 2016-05-18: Working on 把「隐去邮件、企鹅、微信」移至PHP Code中，在数据库中只存原文。
# 关于Exif Tags和图片的旋转：http://stackoverflow.com/questions/4228530/pil-thumbnail-is-rotating-my-image
# 本来想在5月22日的那个周末完成的，奈何因为当天全天都在B.W.F.就没完成。
# 2016-05-26: 附件汇总、上传、附件信息加到Message物件中、与贴文的转换
# 2016-05-29: 非常简陋的根据标题分类的方法
# 2016-06-03: 修正了 MyFix 中的错误
#               1.不能正确处理base64-string形式的标题）
#               2. CSSA=?gb2312?Q?=D0=B6=C8=CE=CD=A8=D6=AA?= 应为“CSSA卸任通知”
# 2016-06-04: 在保存HTML邮件时发现MySQL中的TEXT类型竟然有大小为64KB的限制 … 换成LONGTEXT试试
#             然后把Message中的日期全由datetime.datetime改为时间戳了。
#             副作用波及范围很大 … 改了很多地方
# 2016-06-05: 开始弄bbs->mailinglist的逻辑
# 2016-06-06: Todo: No-GUI时 的 BBS-originated 消息 的 处理
#             新 bug：某人寄了一封没有标题的信，但这封信不会被 parse
# 2016-06-07: 消息与回复目前必须同时可见，也就是说如果有人在6月回复了5月的信息时，5月的信息也需对此程序可见。这是个不完善的地方
#             把数据表中的 标题 一栏 换成了 varchar(512)，因为遇到了一个超长标题的信息（LSU Driving Simulator什么的）
# 2016-06-19: 把内联图片（<img src="cid:XXXX">之类的）、修理「嵌套的<img>标签（形如<img><img></img></img>这样的）」
# 2016-06-21: 修理「在pickle中看到了一个新用户」的情况，使得传给 main.py 的 g_email_to_user 能正常使用。
# 2016-08-23: 添加结巴分词，用来做分词，使搜索功能能够使用
# 2016-09-13: 修改附件的命名方式，把日期部分移去

import email, os, sys, re, pdb, shutil
import email.header
import traceback # http://stackoverflow.com/questions/3702675/how-to-print-the-full-traceback-without-halting-the-program
from bs4 import BeautifulSoup
import codecs
import datetime, dateutil, dateutil.parser
import MySQLdb
import md5, imghdr, Image, base64, pytz
import pickle
from PIL import ExifTags
import jieba.analyse

BOT_SIGNATURE = U"[Mailing List Bot]（无主题）"
FLAG_FROM_MAILING_LIST = 0x01
DEBUG = False

class Attachment:
	def __init__(self):
		self.filehash = None
		self.size = 0
		self.path = None
		self.thumbpath = "[none]"
		self.datetime = None
		self.remote_filename = "[none]"
		self.effective_size = -999

DELIM = "[::]"
class AttachmentManager:
	def __init__(self):
		self.MAX_W = 1024
		self.MAX_H = 640
		self.attachments = dict()
		self.num_append = 0 # 这回增加了多少个附件？
		self.summary = None
	def has_hash(self, h):
		return self.attachments.has_key(h)
	def append(self, h, s, p, dt):
		# 不准使用tab符号
		if p.find(DELIM) != -1:
			print p
			assert False
		#assert p.find('\t') == -1
		entry = Attachment()
		self.attachments[h] = entry
		
		entry.filehash = h
		entry.size = s
		entry.path = p
		entry.thumbpath = "[none]"
		entry.datetime = dt
		entry.remote_filename = "[none]"
		entry.effective_size = -999
		self.num_append += 1
	def LoadFromFile(self, file_name):
		f = codecs.open(file_name, "r", "utf-8");
		for line in f.readlines():
			l = line.strip().split(DELIM)
			h = l[0];
			entry = Attachment()
			entry.filehash = h;
			entry.size = int(l[1])
			entry.path = l[2]
			entry.thumbpath = l[3]
			entry.datetime = int(l[4])
			entry.remote_filename = l[5]
			entry.effective_size = -999
			self.attachments[h] = entry
		f.close()
		print("Loaded attachment manager state from %s" % file_name) 
	def SaveToFile(self, file_name):
		f = codecs.open(file_name, "w", "utf-8")
		for k in self.attachments.keys():
			entry = self.attachments[k]
			p = entry.path
			if not type(p) == unicode: p = p.decode("utf-8")
			tp = entry.thumbpath
			if not type(tp) == unicode: tp = tp.decode("utf-8")
			try:
				f.write(u"%s%s%d%s%s%s%s%s%s%s%s\n" % (k, DELIM, entry.size, DELIM, p, DELIM, tp, DELIM, 
					str(entry.datetime), DELIM,
					entry.remote_filename))
			except Exception as e:
				pdb.set_trace()
		f.close()
		print("Saved attachment manager state to %s" % file_name)
	def PrintStats(self):
		print "Newly appended attachments = %d" % self.num_append
	def DoResize(self, h):
		entry = self.attachments[h]
		p = entry.path
		print p
		assert os.path.exists(p);
		sz_orig = os.path.getsize(p)
		ValidImages = ['gif', 'jpeg', 'png']
		hdr = imghdr.what(p)
		if hdr is not None and hdr in ValidImages:
			img = Image.open(p)
			sz = img.size
			if sz[0] > self.MAX_W or sz[0] > self.MAX_H:
				ratio_w = float(self.MAX_W) / float(sz[0])
				ratio_h = float(self.MAX_H) / float(sz[1])
				ratio = min(ratio_w, ratio_h)
				sz_sm = ( int(ratio*sz[0]), int(ratio*sz[1]) )
				try:
					img_small = img.resize( sz_sm, Image.ANTIALIAS )
				except Exception as e:
					return
				
				# Rotate image according to Exif Tags.
				for orientation in ExifTags.TAGS.keys() : 
					if ExifTags.TAGS[orientation]=='Orientation' : break
				rot = "Not rotated"
				if img.__dict__.has_key("exif"):
					exif = img._getexif()
					if exif:
						exif=dict(img._getexif().items())
						if exif.has_key(orientation):
							if   exif[orientation] == 3 : 
								img_small = img_small.rotate(180, expand=True)
								rot = "Rotated by 180 degrees"
							elif exif[orientation] == 6 : 
								img_small = img_small.rotate(270, expand=True)
								rot = "Rotated by 270 degrees"
							elif exif[orientation] == 8 : 
								img_small = img_small.rotate(90, expand=True)
								rot = "Rotated by 90 degrees"
				
				fn_sm = p + "_small"
				img_small.save(fn_sm, "JPEG")
				sz_small = os.path.getsize(fn_sm)
				entry.thumbpath = fn_sm
				print "Resized to %s, size: %.2f MiB -> %.2f MiB, %s" % \
					(str(sz_sm), sz_orig/1048576.0, sz_small/1048576.0, rot)
				return "scaled"
			else:
				return "no need to scale down"
	def ComputeSummary(self):
		bytes_orig = 0; bytes_small = 0; has_small = 0;
		bytes_effective = 0
		missing_orig = 0; missing_small = 0 # 有多少个文件没有了
		has_remote_path = 0;
		for h in self.attachments.keys():
			entry = self.attachments[h]
			p = entry.path
			s0 = os.path.getsize(p) 
			eff = 0
			sm = entry.thumbpath
			if os.path.exists(p): bytes_orig += s0 
			else: missing_orig += 1
			if sm != "[none]":
				has_small += 1
				if os.path.exists(sm):
					s = os.path.getsize(sm)
					bytes_small     += s
					bytes_effective += s
					eff = s
				else:
					pdb.set_trace()
					missing_small += 1
			else:
				eff = s0
				bytes_effective += s0
			entry.effective_size = eff
			rp = entry.remote_filename
			if rp == "[none]": pass
			else: has_remote_path += 1 
		return {
			"num_files": len(self.attachments.keys()),
			"has_small": has_small,
			"bytes_orig": bytes_orig,
			"bytes_small": bytes_small,
			"missing_orig": missing_orig,
			"missing_small": missing_small,
			"bytes_effective": bytes_effective,
			"has_remote_path": has_remote_path
		}
	def ComputeRemoteFileNames(self):
		allfilenames = set([])
		for e in self.attachments.values():
			if e.remote_filename != "[none]":
				allfilenames.add(e.remote_filename)
		num_gen = 0
		for h in self.attachments.keys():
			entry = self.attachments[h]
			if entry.remote_filename != "[none]":
				continue
			dt = entry.datetime
			p = entry.path
			ValidImages = ['gif', 'jpeg', 'png']
			hdr = imghdr.what(p)
			if not hdr in ValidImages:
				hdr = p[p.rfind('.')+1 :]
				# 2016-06-27:试试看如果无视它会怎么样
				# 有可能是因为图片损坏了 …
				# print "Maybe a corrupt image! header=%s path=%s" % (hdr, p)
				# entry.remote_filename = "[none]"
				# continue
			serial = 1
			while True:
				dt1 = EpochToDateTime(dt)
				n = "%s_%d.%s" % (h, serial, hdr)
				if not n in allfilenames:
					break
				else: serial += 1
			allfilenames.add(n)
			entry.remote_filename = n
			num_gen += 1
		return num_gen
	def PrintSummary(self):
		for h in sorted(self.attachments.keys()):
			entry = self.attachments[h]
			print "Hash:%s RemoteFN:%s" % (h, entry.remote_filename)
	def CopyToLocalRemote(self, destination_dir):
		if not os.path.exists(destination_dir):
			assert False
		if not os.path.isdir(destination_dir):
			assert False
		for h, entry in self.attachments.items():
			if entry.remote_filename != "[none]":
				src = ""
				if entry.thumbpath != "[none]":
					src = entry.thumbpath
				else:
					src = entry.path
				if not os.path.exists(src): assert False
				dest = destination_dir + "/" + entry.remote_filename
				shutil.copy(src, dest)
				print "%s ----copy----> %s" % (src, dest)
		return True
	def PrintHashToFilenameSQL(self):
		print "INSERT IGNORE INTO `stb_mailattachments` VALUES";
		idx = 0
		for h, entry in self.attachments.items():
			if entry.remote_filename != "[none]":
				if idx >= 1: sys.stdout.write(",")
				sys.stdout.write("(\"%s\", \"%s\")" % (h, entry.remote_filename))
				sys.stdout.write("\n")
				idx += 1
				
ATTACHMENT_LOCAL_REMOTE = os.environ["HOME"] + "/Documents/lsu/cssa/mailbackup/LocalRemote"
ATTACHMENT_INDEX_LOCATION = os.environ["HOME"] + "/Documents/lsu/cssa/mailbackup/attachments.txt"
def LoadAttachmentRepository():
	global g_attachmentmanager, ATTACHMENT_INDEX_LOCATION
	if os.path.exists(ATTACHMENT_INDEX_LOCATION):
		g_attachmentmanager.LoadFromFile(ATTACHMENT_INDEX_LOCATION)
		return True
	else: return False
def SaveAttachmentRepository():
	global g_attachmentmanager, ATTACHMENT_INDEX_LOCATION
	g_attachmentmanager.SaveToFile(ATTACHMENT_INDEX_LOCATION)

g_fn = ""
g_not_decoded_fn = []
g_no_plaintext = []
g_idx = 0 # Index of email being processed (global)
g_totalnum = 0 # 一共有多少邮件需要解析。
g_encodings = dict()
g_allencodings = ["utf-8", "gb18030", "gb2312", "ascii"]
for x in g_allencodings: g_encodings[x] = 0
g_allmessages = []
g_allnotifications = []
g_subject_to_message = dict()
g_repeated_subjects = set([])
g_threads = dict()
g_dangling_replies = []
g_allusers = []
g_email_to_user = dict()
g_sender_count = dict() # Email => Count
g_attachmentmanager = AttachmentManager()

# 与SQL导出相关的信息
g_maillist_bot_uid = 2;
g_stb_topic_nodeid = 6;

NODE_NAME_AND_ID = [("未归类", 6),
 ("宠物", 9),
 ("吃喝玩乐", 8),
 ("车", 5),
 ("物品买卖", 3),
 ("租房信息", 4),
 ("音乐", 12),
 ("邮件列表加入／退出", 11),
 ("（回复）", -999),
 ("体育活动", 13),
 ("找帮手", 14),
 ("Carpool", 15),
 ("纠纷／问题处理", 16)
]

# 以下这两项对于主帖与回复皆适用
def NodeNameToNodeID(name):
	for x in NODE_NAME_AND_ID:
		if x[0] == name: return x[1]
	assert False

def NodeIDToNodeName(nid):
	for x in NODE_NAME_AND_ID:
		if x[1] == nid:
			return x[0]
	assert False
	
def ClassifySubject(subject):
	if subject is not None:
		if type(subject) != unicode:
			subject = subject.decode("utf-8")
		subject_l = subject.lower()
		stupid = [
			([u"卖车"], 5),
			([u"租房", u"转租", u"出租", u"合租", u"招租", u"招室友", u"短租", u"找室友", u"求租", u"找房子"], 4),
			([u"甩卖", u"甩賣", u"求购", u"卖东西", u"低价出"], 3),
			([u"加新人"], 11)
		]
		for x in stupid:
			for xx in x[0]:
				if xx in subject: return x[1]
		if u"租" in subject and u"房" in subject: return 4
		if u"租" in subject and u"公寓" in subject: return 4
		if u"招" in subject and u"室友" in subject: return 4
		
		if u"add" in subject_l and u"new" in subject_l and u"member" in subject_l: return 11
		if u"add" in subject_l and "email" in subject_l: return 11
		if u"管理员" in subject and u"邮箱" in subject: return 11
		if u"删除" in subject and u"帐号" in subject: return 11
		if u"加" in subject and u"新人" in subject: return 11
		if (u"添加" in subject or u"删除" in subject) and (u"邮箱" in subject or u"maillist" in subject): return 11
		if u"sign" in subject_l and u"me" in subject_l and u"off" in subject_l: return 11
		if u"sign" in subject_l and "out" in subject_l and "maillist" in subject_l: return 11
		
		if u"signing off" == subject_l: return 11
		if u"添加" in subject and u"新成员" in subject: return 11
		if u"请加" in subject and "@" in subject: return 11
		if u"remove" in subject_l and "email" in subject_l: return 11
		if u"yard sale" in subject_l: return 3
		if u"room for rent" in subject_l: return 4
		if u"sam's" in subject_l and u"卡" in subject_l: return 3 
		if u"for rent" in subject_l and (u"room" in subject_l or u"apartment" in subject_l): return 4
		if u"moving sale" in subject_l: return 3
		if u"賣" in subject and (u"機" in subject or u"箱" in subject): return 3
		if u"卖" in subject and (u"机" in subject or u"箱" in subject or "iphone" in subject_l or u"灯" in subject): return 3
		if u"售" in subject and (u"機" in subject or u"箱" in subject): return 3
		if u"car" in subject_l and u"for sale" in subject_l: return 5
		if u"查" in subject_l and u"vin" in subject_l: return 5
		
		if u"兔子" in subject: return 9
		if u"狗狗" in subject: return 9
		if u"宠物" in subject: return 9
		
		if u"音乐节" in subject: return 12
		if u"晚会" in subject or u"春晚" in subject: return 12
		if "recital" in subject_l: return 12
	
	return 6
	

g_stb_comment_id   = 0; # 当前的
g_stb_topic_id     = 0;
g_stb_user_id      = 3;
g_stb_gid_users    = 3

def GetFolderName(fn):
	x = fn.rfind(".")
	if x != -1:
		fn = fn[0:x]
	return fn
	

def Process1(content):
	content = content.replace("'", "''");  # 给SQL用的。若需要插入的内容是一个单引号，就需要把sql写成两个单引号。
	return content;
	
def Process2(content):
	# 以下的是在Unicode中新添加的表情符。直接在Thunderbird中查看也能看到。
	# 但是，在此版本的MySQL中好像不兼容。 :(
	# 出现在这些信中：《吉他制作》
	# https://codepoints.net/U+1F62C
	
	replacements = [
		(u"\U0001F62C", u"【扮鬼脸】"), # 这个是“Grimacing Face”
		(u"\U0001F3C0", u"【篮球】"), # 这个是“Grimacing Face”
		(u"\U0001F64F", u"【双手合十】"), # "Person with folded hands"
		(u"\U0001F624", u"【鼻孔喷气】"), # "FACE WITH LOOK OF TRIUMPH"
		(u"\U0001F604", u"【弯眉露齿笑】"), # SMILING FACE WITH OPEN MOUTH AND SMILING EYES
		(u"\U0001F607", u"【光环笑脸】"), # SMILING FACE WITH HALO
		(u"\U0001F636", u"【无口笑脸】"), # UNICODE FACE WITHOUT MOUTH
		(u"\U0001F601", u"【Grin】"), # GRINNING FACE WITH SMILING EYES
		(u"\U0001F1F8\U0001F1EA", u"【瑞典国旗】"),
		(u"\U0001F31B", u"【上弦月】"),
		(u"\U0001F1E6", u"[A]"), #
		(u"\U0001F1E7", u"[B]"), #
		(u"\U0001F1E8", u"[C]"), #
		(u"\U0001F1E9", u"[D]"), #
		(u"\U0001F1EA", u"[E]"), #
		(u"\U0001F1EB", u"[F]"), #
		(u"\U0001F1EC", u"[G]"), #
		(u"\U0001F1ED", u"[H]"), #
		(u"\U0001F1EE", u"[I]"), #
		(u"\U0001F1EF", u"[J]"), #
		(u"\U0001F1F0", u"[K]"), #
		(u"\U0001F1F1", u"[L]"), #
		(u"\U0001F1F2", u"[M]"), #
		(u"\U0001F1F3", u"[N]"), #
		(u"\U0001F1F4", u"[O]"), #
		(u"\U0001F1F5", u"[P]"), #
		(u"\U0001F1F6", u"[Q]"), #
		(u"\U0001F1F7", u"[R]"), #
		(u"\U0001F1F8", u"[S]"), #
		(u"\U0001F1F9", u"[U]"), #
		(u"\U0001F1FA", u"[V]"), #
		(u"\U0001F1FB", u"[W]"), #
		(u"\U0001F1FC", u"[X]"), #
		(u"\U0001F1FD", u"[Y]"), #
		(u"\U0001F1FE", u"[Z]") #
	]
	
	for r in replacements:
		content = content.replace(r[0], r[1]); 
	
	content = content.replace("\r\n", "\n")
	content = content.replace("\r", "\n");
	content = content.replace("\n", "<br/>"); # 是HTML格式的。
	content = content.replace("\\@", "@"); # 2016-02-29 发现了。
	
	
	if False:
		# 把邮件地址去掉
		# http://stackoverflow.com/questions/8022530/python-check-for-valid-email-address
		content = re.sub("[a-zA-Z0-9_\.\-]+@[a-zA-Z0-9_\.\-]+\.[a-zA-Z0-9_\.\-]+", u"（邮件地址已隐去）", content)
		# 把微信地址去掉
		content = re.sub("([Ww][Ee][Cc][Hh][Aa][Tt]|微信)\s*[\:是：]?\s*[a-zA-Z0-9\-\+_\.]*", u"（微信已隐去）", content)
		# 把QQ去掉
		content = re.sub("([Qq][Qq]|企鹅)\s*[\:是：]\s*[0-9]+", u"（QQ已隐去）", content)
		# 把电话号码去掉
		content = re.sub("\d\d\d[- ]?\d\d\d[- ]?\d\d\d\d", u"（电话号码已隐去）", content)
		content = re.sub("\d\d\d,\d\d\d,\d\d\d\d", u"（电话号码已隐去）", content)
		
	content = content.replace("\\", "\\\\");
	return content;
	
def ContentToSQLString(content):
	return Process2(Process1(content))
	
# attachments 是 list of hash
def ContentAndAttachmentsToSQLString(content, attachments):
	c = ContentToSQLString(content)
	if len(attachments) > 0:
		c = c + "<lsucssabbs_begin_noninlined_attachments>"
		for a in attachments:
			c = c + "<lsucssabbsatt>%s</lsucssabbsatt>" % a
		c = c + "</lsucssabbs_begin_noninlined_attachments>"
	return c

def DateTimeToEpoch(dt):
	us_central = pytz.timezone("US/Central")
	utc        = pytz.timezone("UTC")
	x = datetime.datetime(year=dt.year, month=dt.month, day=dt.day, \
		hour=dt.hour, minute=dt.minute, second=dt.second)
	x_central = us_central.localize(x)
	t0 = datetime.datetime(1970, 1, 1, 0, 0, 0)
	t0_utc = utc.localize(t0)
	return int((x_central - t0_utc).total_seconds())
	
def EpochToDateTime(epoch):
	us_central = pytz.timezone("US/Central")
	utc        = pytz.timezone("UTC")
	t0 = datetime.datetime(1970, 1, 1, 0, 0, 0)
	t0_utc = utc.localize(t0)
	dt = t0_utc + datetime.timedelta(seconds=epoch)
	return dt.astimezone(us_central)

def ExtractAttachmentHashes(content):
	c = content;
	att = []
	OPEN = "<lsucssabbs_begin_noninlined_attachments>"; CLOSE = "</lsucssabbs_begin_noninlined_attachments>";
	idx0 = c.rfind(OPEN);
	idx1 = c.rfind(CLOSE);
	if idx0 != -1 and idx1 != -1:
		c = c[0:idx0];
		att_c = c[(idx0 + len(OPEN)) : idx1]
		OPEN1 = "<lsucssabbsatt>"; CLOSE1 = "</lsucssabbsatt>";
		while True:
			idx0 = att_c.rfind(OPEN1);
			idx1 = att_c.rfind(CLOSE1);
			if idx0 != -1 and idx1 != -1 and idx1 - idx0 == 47:
				att.append(att_c[ (idx0+len(OPEN)) : idx1 ])
				att_c = att_c[0:idx0]
			else: break
	return c, att

# 此脚本中的email内部表示
class Message:
	def __init__(self, sender, subj, cont, d, attachments, node_id, flag):
		self.primary_key = -999;
		self.subject = subj
		self.sender  = sender
		self.content = cont
		self.date    = d
		self.is_reply = False
		self.parent = None
		self.children = []
		self.last_reply_time = d
		self.attachments = attachments
		self.last_replyer = None # 应该是一个用户类的对象。
		self.order = -999; # 越大的越晚，在主题列表中越靠前
		self.node_id = node_id
		self.flag = flag # 最低位表示“是Mailing List来的信”
		self.parent_hash = None # 用于 db-originated messages
		
		self.old_content = None # 用于资料库升级
		self.keywords = set([])
		
	def updateLastReply(self, r, who):
		if self.last_reply_time is None or r.date >= self.last_reply_time:
			self.last_reply_time = r.date
			self.last_replyer = who;
	def dump(self):
		sys.stdout.write("[%d] [%s]" % (self.primary_key, self.subject))
		if len(self.content) < 40:
			sys.stdout.write("[%s]" % self.content.replace("\n","").replace("\r",""))
		else:
			sys.stdout.write("[%s...]" % (self.content[0:40].replace("\n","").replace("\r","")))
		sys.stdout.write("\n")
	def toSQL(self):
		senddate_ts = self.date
		assert self.primary_key != -999
		if self.is_reply == False:
			assert self.order != -999
			if self.subject == "": subj = BOT_SIGNATURE
			else: subj = self.subject
			if len(self.children) == 0: # No Reply
				return ("INSERT INTO `stb_topics` (`topic_id`, `node_id`, `uid`, `ruid`," + \
					"`title`, `keywords`, `content`, `addtime`, `updatetime`, `lastreply`," + \
					" `views`, `comments`, `favorites`, `closecomment`, `is_top`, `is_hidden`," + \
					"`ord`, `flag`) VALUES " + \
					"(%d, %d, %d, NULL, '%s', NULL, '%s', %d, %d, %d, 0, 0, 0, NULL, 0, 0, %d, %d);") % \
					(self.primary_key, self.node_id, self.sender.uid, \
					 ContentToSQLString(subj), \
					 ContentAndAttachmentsToSQLString(self.content, self.attachments), senddate_ts, senddate_ts, senddate_ts, self.order, self.flag)
			else:
				lastreply_ts = self.last_reply_time
				try:
					return "INSERT INTO `stb_topics` (`topic_id`, `node_id`, `uid`, `ruid`, `title`, `keywords`," + \
						"`content`, `addtime`, `updatetime`, `lastreply`, `views`," + \
						"`comments`, `favorites`, `closecomment`, `is_top`, `is_hidden`, " + \
						"`ord`, `flag`) VALUES " + \
						"(%d, %d, %d, %d, '%s', NULL, '%s', %d, %d, %d, 0, %d, 0, NULL, 0, 0, %d, %d);" % \
						(self.primary_key, self.node_id, self.sender.uid, self.last_replyer.uid, subj, \
						 ContentAndAttachmentsToSQLString(self.content, self.attachments), senddate_ts, lastreply_ts, lastreply_ts, len(self.children), self.order, self.flag)
				except Exception as e:
					pdb.set_trace()
		else:
			return "INSERT INTO `stb_comments` (`id`, `topic_id`, `uid`, `content`, `replytime`, `flag`) VALUES " + \
			       "(%d, %d, %d, '%s', %d, %d);" % \
				   (self.primary_key, self.parent.primary_key, self.sender.uid,
				    ContentAndAttachmentsToSQLString(self.content, self.attachments), senddate_ts, self.flag)
	def toUpdateOrdSQL(self):
		if self.is_reply == False:
			assert self.primary_key != -999
			return "UPDATE `stb_topics` SET `ord`=%d WHERE topic_id=%d;" % \
				(self.order, self.primary_key)
		else:
			assert False
	def toUpdateLastReplySQL(self):
		assert self.primary_key != -999
		return "UPDATE `stb_topics` SET ruid=%d, lastreply=%s, comments=%d WHERE topic_id=%d;" % \
			(self.last_replyer.uid, str(self.last_reply_time), len(self.children), self.primary_key)
	def getHash(self):
		h = ""
		if self.is_reply: 
			h = self.content + "  x  "
		else:
			if self.subject == "": x = BOT_SIGNATURE
			else: x = self.subject
			try:
				h = x + "  x  "+ self.content + "  x  "
			except Exception as e:
				pdb.set_trace()
				exit(1)
		h = Process2(h)
		dt_string = "@".join(str(self.date)) # 如果不这样就会被当作电话号码隐去了。
		return h + dt_string;
	def getOrigin(self):
		if (self.flag & 0x01) == 0x00: return u"BBS"
		else: return u"邮件列表"
	def getFileName(self):
		d1 = EpochToDateTime(self.date).strftime("%Y-%m-%d %H%M")
		fn = "%s - %s - %s - %d.pickle" % (self.subject, self.sender.name,
			d1, self.date)
		fn = fn.replace("/", "_")
		utf8fn = fn.encode("utf-8")
		return utf8fn
	def dumpToPickle(self, f):
		self.children = [] # 不存children
		self.parent = None
		#self.primary_key = -999; # Primary Key 可能会变
		pickle.dump(self, f)

class User:
	def __init__(self, uid, eml, name):
		self.uid = uid     # 只有从DB中读入时才会有UID
		self.email = eml
		self.name = name
		self.num_topics = 0;
		self.num_comments = 0;
		self.dedup_num = None; # 为了消除重复而使用的
		self.regtime = 0;  # Timestamp
		self.lastpost = 0; # Timestamp
		self.firstpost = 0;
		self.num_notifications = 0;
		self.notifications = []
	def __str__(self):
		return u"[{0}]=>[{1}]".format(self.email, self.name)
		#return "[%s,%s]" % (self.email, self.name)
	def getEffectiveName(self):
		if self.dedup_num is None: return self.name
		else: return self.name + str(self.dedup_num) 
	def toSQL(self):
		print self.uid, self.name, self.email, self.num_topics, self.num_comments, self.uid
		sql = "INSERT INTO `stb_users` " + \
			"(`uid`, `username`, `password`, `salt`, " + \
			"`openid`, `email`, `avatar`, `homepage`, " + \
			"`money`, `credit`, `signature`, `topics`, " + \
			"`replies`, `notices`, `follows`, `favorites`, " + \
			"`messages_unread`, `regtime`, `lastlogin`, " + \
			"`lastpost`, `qq`, `group_type`, `gid`, `ip`, " + \
			"`location`, `introduction`, `is_active`, `test_flag`) " + \
			"VALUES ('%d', '%s', NULL, NULL," + \
			"NULL, '%s', 'uploads/avatar/default/', NULL, " + \
			"'0', '100', NULL, '%d', " + \
			"'%d', '0', '0', '0', " + \
			"'0', '%d', NULL, " + \
			"'%d', NULL, '0', '%d', NULL, " + \
			"NULL, NULL, '1', '0');"
		return sql % (self.uid, self.getEffectiveName(), self.email,
				self.num_topics, self.num_comments, 
				self.regtime, self.lastpost,
				g_stb_gid_users,
				)
	def updateLastPost(self, dt):
		if type(dt) == datetime.datetime:
			epoch = DateTimeToEpoch(dt)
		else: epoch = dt
		if epoch >= self.lastpost:
			self.lastpost = epoch
		if self.firstpost == 0 or self.firstpost > epoch:
			self.firstpost = epoch
	def addNotification(self, n):
		if not hasattr(self, 'notifications'):
			self.notifications = []
		self.notifications.append(n)

class Notification:
	def __init__(self, nid, topic, from_user, to_user, ntype, timestamp):
		self.topic     = topic;
		self.from_user = from_user;
		self.to_user   = to_user;
		self.ntype     = ntype;
		self.timestamp = timestamp;
		self.nid       = nid
	def getHash(self):
		return self.topic.getHash() + self.from_user.email + \
			self.to_user.email + str(self.timestamp)
	def toSQL(self):
		return "INSERT INTO `stb_notifications` " + \
			"(`nid`, `topic_id`, `suid`, `nuid`, `ntype`, `ntime`) " + \
			"VALUES ('%d', '%d', '%d', '%d', '%d', '%d'); " % \
			(self.nid, self.topic.primary_key, self.from_user.uid, \
			self.to_user.uid, self.ntype, self.timestamp)
			

# Usage: python argv[0] FOLDER_NAME

# 功能：把形如 “=? XXXX ?=” 这样的编码过的字串拼合成一串（如果前后
#  两段的编码是一样的话。）
# 这样做的原因是：email中的header_decode不能正确处理无编码和有编码
#  放在一起的情况。
# concatenate =? ... ?= 

def MyFix1(x):
	global g_fn;
	ret = []
	last_encoding = "ASCII"
	state = 0; idx0 = 0; idx1 = 0; last_i = 0; i=0
	is_base64 = False
	while i < len(x):
		if i < len(x) - 1:
			if x[i] == '=' and x[i+1] == '?' and state == 0:
				if last_i < i:
					delta = x[last_i:i]
					delta = delta.strip()
					if delta != '': # 空的全不允许。
						ret.append([x[last_i:i], last_encoding]);
				state = 1; idx0 = i; i = i + 2; continue
			elif (x[i] == '?' and (x[i+1] == 'Q' or x[i+1] == 'b' or x[i+1] == 'B')
				and x[i+2] == '?' and state == 1): # Updated on 03-07-2016 & 06-03-2016
				idx1 = i;
				this_encoding = x[idx0+2:idx1]
				if x[i+1] in ('B', 'b'): is_base64 = True
				else: is_base64 = False
				state = 2; i = i + 3; continue
			elif x[i] == '?' and x[i+1] == '=' and state == 2:
				state = 0; 
				if this_encoding == last_encoding:
					tmp = ret[-1][0]
					if not (tmp[-2] == '?' and tmp[-1] == '='):
						pass  # 中间这一段也可以没有说是什么编码的。
					delta = x[idx1+3:i+2]
					if is_base64:
						delta = base64.decodestring(x[idx1+3:i])
					if tmp[-2] == '?' and tmp[-1] == '=':
						last_tmp = tmp[0:-2]
					else: last_tmp = tmp
					ret[-1][0] = last_tmp + delta
					ret[-1][1] = last_encoding
				else:
					try:
						if is_base64: 
							xdecoded = base64.decodestring(x[idx1+3:i])
							ret.append([base64.decodestring(x[idx1+3:i]), this_encoding])
						else: ret.append([x[idx0:i+2], this_encoding])
					except Exception as e:
						pdb.set_trace()
						assert False
				last_encoding = this_encoding;
				i = i + 2; last_i = i; continue
			else:
				i=i+1;
				continue
		else:
			i = i+1; 
			continue;
	if i > last_i:
		ret.append([x[last_i:i+1], last_encoding])
	return ret

def IsBlacklist(x):
	if x in (' ', '\r', '\n'): return True

def RemoveNewLines(x):
	ret = x.replace('\n', '')
	ret = ret.replace('\r', '')
	return ret

def ExtractMySenderNameEmail(x):
	m = re.match(".*<(?P<email>.*@.*)>.*", x)
	if m:
		sender_name  = x[:m.start("email")-1].strip()
		sender_email = m.group("email").lower()
		return (sender_name, sender_email)
	else:
		return (x, "Unknown")

def ExtractMySubject(subj):
	if subj is None:
		return ("", "ASCII");
	is_valid = False
	chunks_and_encodings = MyFix1(subj)
	h = ""
	the_charset = None
	#print
	#print subj
	for chunk_and_encoding in chunks_and_encodings:
		try:
			hdr = email.header.decode_header(chunk_and_encoding[0]) # 功能是把 字串化的 octets 转成 binary octets
	#		print hdr
		except Exception as e:
			print "chunk =", chunk_and_encoding[0]
			print "subj  =", subj
			print e
			assert False
		is_valid = True
		for x in hdr:
			if type(x[0]) == unicode:
				delta = x[0]
			else:
				if x[0] is None and x[1] is None:
					is_valid = False
					break
				ok = False
				try:
					delta = unicode(x[0], chunk_and_encoding[1])
					ok = True
				except Exception as e:
					pass
				
				try:
					if not ok:
						delta = unicode(x[0], "gb18030")
						ok = True
				except Exception as e:
					return (None, None)
				
			if not IsBlacklist(delta):
				h = h + delta
			if x[1] is not None:
				the_charset = x[1];
	if is_valid:
		h = RemoveNewLines(h)
	#print h
	return (h, the_charset) # May Be Untitled

def GuessRootParent(subj):
	ret = None
	needles = [u"Re:", u"Re :", u"回复:", u"回复："]
	while True:
		is_found = False;
		for n in needles:
			idx = subj.find(n)
			if subj.find(n) == 0:
				subj = subj[len(n):].strip()
				ret = subj
				is_found = True;
				break;
		if not is_found: break;
	return ret
	
# parse_stack 加上 full_content_type 才是现在的完整的 栈
def do_SavePart(full_content_type, part, parse_stack, the_idx):
	if parse_stack == "": fn01 = full_content_type
	else: fn01 = "-".join(parse_stack) + "-" + full_content_type
	fn1 = "%03d-%s" % (the_idx[0], fn01)
	suffix = ""
	if full_content_type.endswith("jpeg"): suffix = ".jpg"
	elif full_content_type.endswith("text/plain"): suffix = ".txt"
	elif full_content_type.endswith("text/html"): suffix = ".html"
	fn1 = "out/" + fn1.replace("/", "_") + suffix;
	
	if type(part) == str: pl = part
	else: pl = part.get_payload(decode=True);
	
	if pl is None: return
	
	f_pl = open(fn1, "wb")
	f_pl.write(pl)
	f_pl.close()

def do_SaveImagePart(email_fn, part, all_content_ids, all_img_hashes, content_id_to_hash,
	attachments, image_idx, dt):
	global g_attachmentmanager
	cid = part["Content-ID"]
	if cid is not None:
		if cid[0] == '<' and cid[-1] == '>':
			cid = cid[1:-1]
		all_content_ids.add(cid)
	
	folderpath = GetFolderName(email_fn)
	if not os.path.exists(folderpath):
		os.mkdir(folderpath)
	#x = part._headers[0][1] # "('Content-Type', 'image/jpeg; name="c.jpg"')"
	fn_atchmt = None
	for xx in part._headers:
		xx = xx[1]
		
		# 2016-06-03 发现bug，ExtractMySubject 不能正常解析 "=?UTF-8?b?5bqKICgxKS5KUEc=?="        ----修理完了
		if "name=" in xx:
			fn_atchmt = xx.split("name=")[1].replace("\"", "")
			fn_atchmt = ExtractMySubject(fn_atchmt)[0];
			if fn_atchmt is None:
				pdb.set_trace()
			fn_atchmt = fn_atchmt.strip()
			if '; x-apple-part-url' in fn_atchmt:
				fn_atchmt = fn_atchmt.split("; x-apple-part-url")[0]
			break
		elif "filename*" in xx:
			fn_atchmt = re.match("[\s\S]*filename\*\d\=(?P<x>[\s\S]*)", xx).group("x")
		else:
			fn_atchmt = "image" + str(image_idx[0])
	if fn_atchmt == None:
		pdb.set_trace()
		print "Offending header: " + str(part._headers)
		assert False
	if not type(folderpath) == unicode: folderpath = folderpath.decode("utf-8")
	
	payload = part.get_payload(decode=True)
	m = md5.new(); m.update(payload);
	h = m.hexdigest()
	
	if fn_atchmt == "assert.png":
		fn_atchmt = h
	destination = u"%s/%s" % (folderpath, fn_atchmt)
	#print "Folder is " + folderpath
	#print "Image should go to " + destination
	
	attachments.append(h)
	
	if not g_attachmentmanager.has_hash(h):
		g_attachmentmanager.append(h, len(payload), destination, dt)
		with open(destination, "wb+") as f:
			f.write(payload);
			f.close();
		g_attachmentmanager.DoResize(h) # 需要先存然后再缩小
	image_idx[0] += 1;
	
	all_img_hashes.add(h)
	if cid is not None:
		content_id_to_hash[cid] = h

def DumpEmailPart(full_content_type, part, indent, the_idx, parse_stack):
	global DEBUG
	if DEBUG:
		print ("[DEBUG][%3d]" % the_idx[0]) + " " + "  " * indent + full_content_type
		the_idx[0] += 1
		next_stack = parse_stack + [full_content_type]
		if full_content_type == 'message/rfc822':
			for sub_part in part.walk():
				ct_sub = sub_part.get_content_type()
				DumpEmailPart(ct_sub, sub_part, indent + 1,
					the_idx, next_stack + [ct_sub])
		elif full_content_type.startswith('multipart'):
			for sub_part in part.get_payload():
				ct_sub = sub_part.get_content_type()
				DumpEmailPart(ct_sub, sub_part, indent + 1,
					the_idx, next_stack + [ct_sub])
		else:
			do_SavePart(full_content_type, part, parse_stack, the_idx)

def AnalyzeOneEmail(fn):
	global g_idx, g_fn, g_email_to_user, g_allusers, DEBUG
	g_idx += 1

	# 印一下。
	if not DEBUG:
		if (g_idx % 100) == 1 or g_idx == g_totalnum:
			sys.stdout.write("\n %d/%d" % (g_idx, g_totalnum))
			sys.stdout.flush()
		else:
			sys.stdout.write(".")
			sys.stdout.flush()

	if os.path.isdir(fn): return # 可能是附件目录。是的话就要跳过。
	g_fn = fn
	f = open(fn)
	
	if fn.endswith(".pickle"): 
		eml = pickle.load(f)
		if eml.__class__.__name__ == "Message":
			sender = eml.sender
			if not g_email_to_user.has_key(sender.email):
				g_email_to_user[sender.email] = sender
			if g_sender_count.has_key(sender.email):
				eml.sender = g_email_to_user[sender.email]
			g_allmessages.append(eml)
			f.close()
			return
		else:
			return
	
	eml = email.message_from_file(f)
		
	h = ""; charset = "ASCII"
	subj   = eml["Subject"]
	tmp, _ = ExtractMySubject(eml["From"])
	sender_name, sender_email = ExtractMySenderNameEmail(tmp)
	sender = None
	if g_email_to_user.has_key(sender_email) == False:
		sender = User(-999, sender_email, sender_name)
		g_email_to_user[sender_email] = sender
		g_allusers.append(sender)
	else:
		sender = g_email_to_user[sender_email]
	body   = eml["Body"]
	dt     = eml["Date"]
	is_valid = True;
	has_plaintext = False;
	parent = None;

	if subj is not None and dt is not None:
		(h, charset) = ExtractMySubject(subj)
		subj = h
		parent = GuessRootParent(subj)
		if parent is not None:
			if not g_threads.has_key(parent):
				g_threads[parent] = [None, set([])] # Root msg, Replies
	else:
		is_valid = False;

	nodeid = ClassifySubject(subj)
	
	attachments = []
	image_idx = [0]
	if is_valid:
		us_central = pytz.timezone("US/Central")
		utc        = pytz.timezone("UTC")
		date_tuple = email.utils.parsedate_tz(eml["Date"])
		naive_datetime = datetime.datetime.utcfromtimestamp(email.utils.mktime_tz(date_tuple))
		utc_datetime = utc.localize(naive_datetime)
		dt = DateTimeToEpoch(utc_datetime.astimezone(us_central))
		sender.updateLastPost(dt)
		allcontent_plain = ""
		allcontent_html_old = ""
		allcontent_html  = []
		if DEBUG: print "[DEBUG] Begin email walk"
		part_idx = [0]
		content_id_to_hash = dict()
		all_img_hashes     = set([])
		all_content_ids    = set([])
		for part in eml.walk():
			
			mt = part.get_content_maintype();
			fullt = part.get_content_type()
			
			if DEBUG:
				DumpEmailPart(fullt, part, 0, part_idx, [])
					
			if mt == "image": 
				do_SaveImagePart(fn, part, all_content_ids, all_img_hashes, content_id_to_hash,
					attachments, image_idx, dt)
				
				continue

			mt = part.get_content_type();
			if mt not in set([
				"application/octet-stream",
				"multipart/alternative",
				"multipart/related",
				"application/vnd.openxmlformats-officedocument.wordprocessingml.document", # 某一封信里有这个，暂且先忽略之
				"application/pdf", # PDF附件；
				"application/zip", # Zip附件
				]):
				orig_charset = part.get_charset()
				payload = part.get_payload(decode=True)
				content = payload

				for cs in g_allencodings:
					try:
						content = payload.decode(cs);
						has_plaintext = True;
						g_encodings[cs] += 1;
						#print "This part is encoded using %s", cs
						break;
					except Exception as e:
						#print "This part is not encoded using %s", cs
						continue
				assert "This string is not encoded using any known coding!"

				if content is None: continue
				try:
					# 2016-06-04：论坛可以直接显示HTMl，所以可以不用转换
#					content = nltk.clean_html(content) # Remove HTML stuff # 不该再用这个nltk了。该用beautiful soup
#					soup = BeautifulSoup(content, "html.parser")
#					content = soup.get_text()
					content = content;
				except Exception as e:
					print e
					print "Offending HTML:", content
					exit(1)

				try:
					if mt == "text/plain":
						allcontent_plain += content
						
						# 2016-06-04：虽然论坛可以直接显示HTML 但是有会影响页面上其它元素的问题
					elif mt == "text/html":
						soup = BeautifulSoup(content, "html.parser")
						parsed = soup.get_text().strip()
						if parsed != "":
							allcontent_html.append(content)
							allcontent_html_old += parsed
							
				except Exception as e:
					print
					print e
					print "Offending content:", content
					print "Type:", mt
					traceback.print_exc()
					exit(0)
#		print "Email Content:", allcontent[0:100].replace("\n","")
	if not has_plaintext:
		g_no_plaintext.append(fn);
	else:
		
		# 旧版DB
		if allcontent_html_old == "": allcontent_old = allcontent_plain
		else: allcontent_old = allcontent_html_old
		
		inlined_hashes = set([])
		all_html_out = []
		is_replaced = False
		for content in allcontent_html:
			root_imgs = set([])
			standalone_imgs = set([])
			imgs_tags_and_insertion_points = []
			soup = BeautifulSoup(content, "html.parser")
			
			# 替换所有的images
			# 第一步：找到所有的<img>和相互嵌套的<img>'s，
			#   并把插入点记下来
			# 到最后， standalone_imgs 里面只会有parent非img的叶子img结点
			imgs = soup.find_all('img')
			is_replaced = False
			for i in imgs:
				if i.attrs.has_key('src'):
					img_src = i.attrs['src']
					if img_src.startswith('cid:'):
						cid = img_src[4:]
						if content_id_to_hash.has_key(cid):
							h = content_id_to_hash[cid]
							new_tag = soup.new_tag('div')
							new_tag.string = ""
							new_tag["style"] = 'border:1px gray dotted; color:gray'
							new_tag1 = soup.new_tag("lsucssabbsatt")
							new_tag1.string = h
							new_tag.append(new_tag1)
							if i.parent.name != 'img':
								imgs_tags_and_insertion_points.append((i, new_tag, i.parent))
								standalone_imgs.add(i)
							else:
								p = i.parent; last_p = None
								while p.name == 'img':
									if p in standalone_imgs:
										standalone_imgs.remove(p)
									last_p = p
									p = p.parent
								root_imgs.add(last_p)
								imgs_tags_and_insertion_points.append((i, new_tag, p))
								assert i.parent is not None
							
							inlined_hashes.add(h)
							is_replaced = True
						else:
							print "CID not found: %s, filename=%s", (cid, fn)
							
			# 第二步：擦除原有的<img>标签
			for ri in root_imgs:
				print "Decomposed"
				ri.decompose()
			
			# 第三步：
			for idx in xrange(len(imgs_tags_and_insertion_points)-1, -1, -1):
				i_t_p = imgs_tags_and_insertion_points[idx]
				#if i_t_p[0].parent is not None and i_t_p[2].parent is not None:
				if len(soup.find_all("body")) > 0:
					if i_t_p[0] in standalone_imgs:
						if i_t_p[0].parent is not None:
							i_t_p[0].replace_with(i_t_p[1])
						else: # 2016-10-28: 有些时候parent会是Null，就加到文档的最后去
							soup.find_all("body")[0].insert(-1, i_t_p[1])
					else:
						if i_t_p[2].parent is not None:
							i_t_p[2].insert_after(i_t_p[1])
						else: # 2016-10-28: 有些时候parent会是Null，就加到文档的最后去
							soup.find_all("body")[0].insert(-1, i_t_p[1])
					
			all_html_out.append(str(soup))
		
		allcontent_html = "".join(all_html_out)
		allcontent_html = allcontent_html.decode("utf-8")
		
		if is_replaced and DEBUG:
			print u"替换了<img>以后的html：", allcontent_html
		
		if allcontent_html != "": 
			allcontent = allcontent_html; flag_html = 0x02
		else: 
			allcontent = allcontent_plain; flag_html = 0x00;
		
		# 如果一个附件已经被inline了，那就不要再把它当作attachments了
		not_inlined_attachments = []
		for a in attachments:
			if not a in inlined_hashes:
				not_inlined_attachments.append(a)
		
		flag_att = 0;
		if len(not_inlined_attachments) > 0:
			flag_att = 4
		
		m = Message(sender, subj, allcontent, dt, 
			not_inlined_attachments, -999, 
			FLAG_FROM_MAILING_LIST | flag_html | flag_att)
		m.old_content = allcontent_old
		g_allmessages.append(m)
		if parent is not None:
			g_threads[parent][1].add(m)
			m.is_reply = True;
			m.node_id = -999;
		else:
			m.is_reply = False;
			m.node_id = nodeid;
		if g_sender_count.has_key(sender_email) == False:
			g_sender_count[sender_email] = 0
		g_sender_count[sender_email] += 1
	
	if DEBUG:
		print "===========DEBUG==========="
		print "Subject     :", subj
		print "Sender Name :", sender_name 
		print "Email       :", sender_email
		print "Date        :", dt

	f.close()

def AnalyzeFolder(fn):
	global g_cwd;
	files = os.listdir(fn)
	for f in files:
		if os.path.isdir(f): continue
		else: 
			full_fn = fn + "/" + f
			AnalyzeOneEmail(full_fn)

# ----从D.B.中把所有的主题和回复都拉出来。 ----#
def GetAllMessagesFromDB():
  assert 0

# DB 中的 帖子 经过了 替换；
# 而 eml 中的 帖子 还没有经过替换。
def DiffDBAndEMLFiles(db_mails, eml_mails):
	db_contents = set([])
	for m in db_mails:
		db_contents.add(m.content)
	set11 = set([]); # 在eml文件中，也在DB中
	set10 = set([]); # 在eml文件中，但不在DB中（很有可能是新进邮件）
	for m in eml_mails:
		key = ContentToSQLString(m.content)
		if key in db_contents:
			set11.add(m)
		else:
			set10.add(m)
	print "%d emails in eml files on disk but not in DB" % len(set10)
	print "%d emails in both eml files and DB" % len(set11)

# Step 0: Launching Mode.

# Beware of the side effects
def ComputePrimaryKeys(start_topic_id, start_comment_id):
	tid = start_topic_id; cid = start_comment_id;
	for m in g_allmessages:
		if m.is_reply == False:
			m.primary_key = tid;
			m.order = tid;
			tid += 1;
			# 把回复也排序。
		else:
			m.primary_key = cid;
			cid += 1;

def SortAndConstructThreads():
	global g_allmessages, g_threads, g_repeated_subjects,  \
		g_subject_to_message, g_stb_topic_id, g_stb_comment_id, \
		g_allnotifications
	# Step 2: Compute Stupid Thread Hierarchy
	
	# Step 2.5: 对于originated in bbs的，需要topic_id => Message
	hash_to_topic = dict()
	
	for m in g_allmessages: 
		if (m.flag & 0x01 == 0x01):
			if g_threads.has_key(m.subject):
				if not (g_threads[m.subject][0] is None):
					g_repeated_subjects.add(m.subject)
				g_threads[m.subject][0] = m
				if not g_subject_to_message.has_key(m.subject):
					g_subject_to_message[m.subject] = set([])
				g_subject_to_message[m.subject].add(m)
		else:
			m.updateLastReply(m, m.sender)
		if m.is_reply == False:
			hash_to_topic[m.getHash()] = m

	# Step 2.1: Assign Primary Keys to Theme Heads
	# 先按發表時間排序。
	g_allmessages = sorted(g_allmessages, key = lambda x : x.date, reverse = False)
	ComputePrimaryKeys(g_stb_topic_id, g_stb_comment_id);

	# Step 3: Print Outputs and add to children
	print 
	print "All %d successfully parsed messages." % len(g_allmessages)
	for thd, allposts in g_threads.items():
		if allposts[0] is None:
			pass
		else:
			for reply in allposts[1]:
				reply.is_reply = True
				reply.parent = allposts[0]
				allposts[0].children.append(reply)
				allposts[0].last_replyer = reply.sender
				allposts[0].updateLastReply(reply, reply.sender)
				
	# Step 3.5: DB-Originated comments
	for m in g_allmessages:
		if (m.flag & 0x01 == 0x00):
			# 先把「最后回复者」刷成自己
			m.updateLastReply(m, m.sender)
			if m.is_reply:
				if not hash_to_topic.has_key(m.parent_hash):
					print "Dangling DB-originated cmt",
					print m.content
					print m.parent_hash
					continue
				p = hash_to_topic[m.parent_hash]
				p.children.append(m)
				p.last_replyer = m.sender
				m.parent = p
				p.updateLastReply(m, m.sender)
				print m.last_reply_time, m
	
	# Step 4: Sort children
	for m in g_allmessages:
		if m.is_reply == False:
			m.children = sorted(m.children, key = lambda x : x.date, reverse = False)
			
			
	# Step 5: Print out and construct Notifications
	for m in g_allmessages:
		if m.is_reply == False:
			print "[%s]" % (m.subject)
			for c in m.children:
				n = Notification(-999, m, c.sender, m.sender, 1, c.date)
				g_allnotifications.append(n)
				m.sender.addNotification(n)
				print "    [%s by %s]" % (c.subject, c.sender.email)

def foo():
	print ExtractMySubject("=?GB2312?Q?Bogdan_Vladu=A3=BACut_the_rope_game_using_SpriteKit_=2D_P?=\n =?GB2312?Q?art2_Sneek_Peek?=")
	print ExtractMySubject("=?UTF-8?B?6YKT5p+v6K+E44CK5oiR5piv5q2M5omL44CL77yI56ys5LqM?==?UTF-8?B?5a2j77yJ4oCU4oCU55uQ57O75YiX5Y2B5LiA5pyI5paw5Lmm?=")
	print ExtractMySubject("=?GB2312?B?y66raIO6o7rP4Mu82XjT6NVsIGJ5IERpemk=?=")
	print ExtractMySubject("=?UTF-8?Q?=E6=B1=82=E8=B4=AD=E6=95=8C=E6=95=8C=E7=95=8F=E6=9D=80=E8=99?= =?UTF-8?Q?=AB?=")

if __name__ == "__main__":
	
	if sys.argv[1] == "--attachments":
		if LoadAttachmentRepository():
			if len(sys.argv) < 3:
				print "处理附件。"
				x = g_attachmentmanager.ComputeSummary()
				print "一共有 %d 个附件、其中 %d 个应该有对应的缩小版。" % (x["num_files"], x["has_small"])
				print "原尺寸的附件总大小为 %.2f MiB。总共占据的空间为 %.2f MiB。" % (x["bytes_orig"] / 1048576.0, x["bytes_effective"] / 1048576.0)
				print "其中缩小版占据的空间为 %.2f MiB。" % (x["bytes_small"] / 1048576.0)
				if x["missing_orig"] > 0: print "这些附件中有 %d 个原尺寸的找不到了。" % x["missing_orig"]
				else: print "原尺寸附件看起来都正常。"
				if x["missing_small"] > 0: print "这些附件中有 %d 个缩小版的找不到了。" % x["missing_small"]
				else: print "缩小版的附件看起来都正常。"
				print "其中有 %d 个有对应的远端文件名。" % x["has_remote_path"]
				exit(0)
			else:
				if sys.argv[2] == "prepareremote":
					x = g_attachmentmanager.ComputeRemoteFileNames()
					SaveAttachmentRepository()
					print "计算好了远端文件路径了。新增了 %d 个。" % x
					print "需要把以下的对应表加入到数据库中："
					g_attachmentmanager.PrintHashToFilenameSQL()
					exit(0)
				elif sys.argv[2] == "copytolocalremote":
					g_attachmentmanager.CopyToLocalRemote(ATTACHMENT_LOCAL_REMOTE)
					exit(0)
				elif sys.argv[2] == "printsummary":
					g_attachmentmanager.PrintSummary()
					exit(0)
		else:
			print "啊！附件的repository并没有准备好的样子。"
			exit(1)
	
	elif sys.argv[1] == "--classify":
		f = open(sys.argv[2])
		hist = dict()
		nc = 0; totcount = 0
		for line in f:
			line = line.strip()
			if line[0] == '"' and line[-1] == '"':
				line = line[1:(len(line)-1)]
			nid = ClassifySubject(line)
			if not hist.has_key(nid):
				hist[nid] = 0
			hist[nid] += 1
			if nid == 6:
				print line, nid, NodeIDToNodeName(nid)
			else: pass
			
			if nid == 6: nc += 1
			totcount += 1
		
		for k, v in hist.items():
			print k, v
		
		print "%d / %d Not classified" % (nc, totcount)	
		exit(0)

	elif sys.argv[1] == 'single':
		DEBUG = True
		p = sys.argv[2]
		if p[0] == '/': full_path = p
		else: full_path = os.getcwd() + '/' + p
		AnalyzeOneEmail(full_path)
		exit(0)
	
	LoadAttachmentRepository()
	
	# Step 1: Parse all messages
	g_cwd = os.getcwd()
	g_use_db = False;
	if len(sys.argv) <= 1: dirs=["."]
	else:
		if sys.argv[1] == "--testdb":
			g_use_db = True;
			dirs = sys.argv[2:]
		else:
			dirs = sys.argv[1:]

	# 统计一下一共有多少邮件需要 parse。
	for x in dirs:
		if x[0] == '/':
			files = os.listdir(x)
		else:
			files = os.listdir(g_cwd + "/" + x)
		g_totalnum += len(files)

	print "Total %d files." % g_totalnum
	# 然后就 parse 。
	for x in dirs:
		if x[0] == '/':
			AnalyzeFolder(x)
		else:
			AnalyzeFolder(g_cwd + '/' + x)

	SortAndConstructThreads() # 如果只是要Parse试一试的话，primary_key不会用到。所以设定为0也没关系。

	print 
	print "The following %d subjects may correspond to 1+ threads:" % len(g_repeated_subjects)
	for s in g_repeated_subjects:
		print "[%s]" % s
		for x in g_subject_to_message[s]:
			sys.stdout.write("  ")
			x.dump()

	print
	print "The following %d email files have no text/plain payload:" % len(g_no_plaintext)
	for x in g_no_plaintext:
		print x

	print
	print "Encoding Histogram w.r.t Parts of Messages:"
	for k, v in g_encodings.items():
		print k, v

	if not g_use_db:
		# Step 3.1: Print SQL Statements
		# 只有一層，不用遞歸。
		f_sql = codecs.open("sql.txt", "w")
		tmp = set([])
		for m in g_allmessages:
			if m in tmp: continue
			if m.is_reply == False:
				#print m.toSQL();
				f_sql.write((m.toSQL() + "\n").encode("utf8"));
				tmp.add(m)
				for r in m.children:
					if r in tmp: continue
					#print r.toSQL(); 
					tmp.add(r)
					f_sql.write((m.toSQL() + "\n").encode("utf8"));
			else:
				if m.parent is None:
					g_dangling_replies.append(m)
				else:
					#print m.toSQL(); 
					tmp.add(m)
					f_sql.write((m.toSQL() + "\n").encode("utf8"));
		f_sql.close()

		print
		print "有 %d 则回复没有找到其对应的主帖。可能这些主帖不在范围内（比如五月的帖子在六月时收到了一则回复）", len(g_dangling_replies)
		print "Outputs saved to \"sql.txt\""
	else:
		dbmails = GetAllMessagesFromDB()
		DiffDBAndEMLFiles(dbmails, g_allmessages)

	print "Total %d distinct senders" % len(g_allusers)
#	for x in g_allusers:
#		print unicode(x), g_sender_count[x.email], "post/s"
#		print "%s, %d posts" % (str(x), g_sender_count[x.email])
	SaveAttachmentRepository()

else:
	print "邮件解析单元装入了。"
