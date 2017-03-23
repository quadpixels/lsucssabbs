# -*- coding: utf-8 -*-

# Stolen from here:
#   http://pythonforengineers.com/your-first-gui-app-with-python-and-pyqt/
# and here:
#   https://gist.github.com/skriticos/5415869
#
# 2016-02-26 TODO项：
#   ※ 更新「回复的内容」
#   ※ 更新「在插入新帖子时给出正确的用户发帖数&回帖数」
# 2016-02-29
#      数据库的Collate必要设为utf8_unicode_ci。
#      问题：为何最后一封topic的topic_id会突然变大很多呢？
#        原来是每次解析完一个文件夹再insert就会突然变大到3127之多。
#        原来主键=topic_id不能为0.
#   ※ 清除数据库的功能
# 2016-03-01
#   ※ 在一则新回复发表时，其所在的主题帖也需要更新={最后回复的人的UID、最后回复时间}。
#      查找回复所对应的主题的primary_key时有问题 …
#    问题：有些帖子已经塞入db了，但在再次扫eml的时候认为并不在db中。为什么呢。
#    是因为虽然在eml中的内容是     “……这个邮件【乱码】【乱码】<br/><br/>Sent from my iPhone]“，
#    但是在插入数据库以后内容变成了 “……这个邮件“，
#    也就是说，乱码以及乱码之后的内容没有了。
# 2016-03-08
#   ※ 修正时区的问题。存入database的永远应该是UTC时区的时间戳。显示时所用之时区需要在index.php中设定。
# This is Kode Spaghetti! 怎么办呢。
# 2016-05-08
#   ※ 在新增用户后，同时更新「最新会员」
# 2016-05-16 把排序用一行sql改写了一下，无论一次更新多少都是一条SQL查询，排序更新速度大幅增加。
#
# 需要完成的功能：
#   ＊ 每日统计 done on 2016-03-03
#   ＊ 从信箱拉取邮件 done on 2016-03-07
#   ＊ 用已注册的邮箱登录、修改用户名 done on 2016-05-08
# 2016-05-26 
#   Todo：更新每个分类的帖子数、自动统计+上传附件、用户的Statistics
# 2016-05-28
#   把附件管理员整到GUI中了
# 2016-05-29
#   ＊ (FTP)拉取已经在远端的附件的信息
#   ＊ (SQL)附件索引

#   ＊ 把本地的分类更新到远端 - 应该和解析同时完成，然后再在Statistics中更新计数
#   ＊ 在GUI中上传附件到FTP（用独立的线程）
#   ＊ 还要把从cssalsu.official发给mailing list的信也存下来（因为它不会出现在inbox里）
#   New Issue：不能编辑有附件的帖子，会把附件给escape掉
#   ＊ 无GUI版本的更新流程初步完成了，需要测试几天才知道稳定性如何
# 2016-05-31
#   ＊ 把时区的处理弄清楚了，即是先统一把没有时区的Naive Datetime Object转换成有时区的Aware Datetime Object，然后再经由UTC时区从不同的时区转换。（有些信息是Asia/Beijing的时区，但是在解析中，用的是US/Central时区）
# 2016-06-01
#   ＊ 开始翻看以前的旧邮件。 -----------〉 啊！官方邮箱里的邮件很多被删掉了，特别是2015年11月和12月的。猜是为了省空间。
#   Bug修正之前不能解析的邮件有：
#       2015年6月19日、2015年6月25日
#   修正完了就可以解析了。
# 2016-06-04
#   ＊ 在退出时，把界面中几个输入框里的内容保存下来
#   ＊ 加一个Flag给stb_topics，用来表示帖子的附加属性，比如是否来自Mailing List
# 2016-06-05
#   ＊ 修正用户注册时间
#   ＊ 开始编写 BBS ----> Mailing List 这个方向的更新的逻辑
#      在parse时需要注意 从BBS来的信息的 hierarchy
# 2016-06-07: No-GUI时 的 BBS-originated 消息 的 处理
#             但是现在因为没有全局的index，只能一次读入所有的信息再处理其中的回复依赖关系
# 2016-06-14: Notifications的计算；出于让流程变简单的目的，做成了「statistics」的一部分
# 2016-06-17: 对于GUI模式下的View的更新有微小的重构
# 2016-06-19: 支持更新数据版本 … 在今天会有一次对所有带有附件的topic的更新…
# 2016-06-23: 需要处理当主帖不存在时的通知更新的情况
# 2016-07-09: 文件名太长，截断之
# 2016-07-16: WPChina空间拒绝SFTP连接，先暂时换成不加密的FTP。
# 2016-12-24: 容量超出，不得不删除一些巨占空间的回复，而这也造成了数据不一致性，需要处理这些情况
# 2017-03-21: Classify routine connected to ``classify'' button

from PyQt4 import Qt, QtCore, QtGui, uic
from PIL import ExifTags
import sys, os, datetime, imaplib, email, email.header, email.generator, email.parser, time, codecs
import analyze
import MySQLdb, ftplib, re, pdb, pytz
import pickle
import jieba.analyse
from bs4 import BeautifulSoup

g_configs = dict()
g_lastsave = dict()

import myconfigs
do_loadconfigs = myconfigs.do_loadconfigs

DATEFMT = "%Y-%m-%d %H:%M:%S"
ui_filename = "mailinglist.ui"
Ui_MainWindow, QtBaseClass = uic.loadUiType(ui_filename)

SEP="[::]"

def GetMessageSummary(msgs):
	num_head = 0; num_reply = 0;
	tmp = set([])
	for x in msgs:
		if x.is_reply == False:
			if x in tmp: continue
			tmp.add(x)
			num_head += 1;
		else:
			if x in tmp: continue
			tmp.add(x)
			num_reply += 1;
	return u"%d篇文章，其中有%d封主题，%d封回复" % \
		(num_head + num_reply, num_head, num_reply)
def GetSendersSummary(x):
	return "%d users" % len(x)
def SetBackgroundColorQTreeWidgetItem(x, color):
	for i in range(0, x.columnCount()):
		x.setBackgroundColor(i, QtGui.QColor(color))
		
class AttachmentManagerThread(QtCore.QThread):
	signal_completed = QtCore.pyqtSignal(object, object) # summary, attachments
	def __init__(self, x):
		QtCore.QThread.__init__(self)
		self.index_location = x["index_location"];
		self.local_remote   = x["local_remote"];
	def run(self):
		analyze.g_attachmentmanager.LoadFromFile(self.index_location);
		summary     = analyze.g_attachmentmanager.ComputeSummary()
		analyze.g_attachmentmanager.ComputeRemoteFileNames()
		attachments = analyze.g_attachmentmanager.attachments.values()
		self.signal_completed.emit(summary, attachments)

# 为了能Hash，所以新建一个类
class RemoteAttachment:
	def __init__(self, fn, sz, dt):
		self.filename = fn
		self.size = sz
		self.mtime = dt

# FTP 的 用法 参考这里： http://stackoverflow.com/questions/17417513/python-ftp-query
class RemoteFTPAttachmentListThread(QtCore.QThread):
	signal_completed = QtCore.pyqtSignal(object)
	def cb1(self, line):
		x = line.split(" ")
		assert len(x) == 2
		filename = x[1].strip()
		xx = x[0].split(";")
		kvs = dict()
		for kv in xx:
			if "=" not in kv: continue
			tmp = kv.split("=")
			assert len(tmp) == 2
			kvs[tmp[0]] = tmp[1]
		if kvs["type"] == "cdir" or kvs["type"] == "pdir": 
			return # 当前目录 或 上级目录
		sz = int(kvs["size"]);
		m = kvs["modify"]
		dt = datetime.datetime(int(m[0:4]), int(m[4:6]), int(m[6:8]), int(m[8:10]), int(m[10:12]))
		self.remote_attachments.append(RemoteAttachment(filename, sz, dt))

	def __init__(self, x):
		QtCore.QThread.__init__(self)
		self.hostname = x["hostname"]
		self.username = x["username"]
		self.password = x["password"]
		self.path     = x["path"]
		self.remote_attachments = []
		
	def run(self):
		#if self.hostname == "127.0.0.1" or self.hostname == "10.42.0.1": # 如果传到本地机器，可以用明文传输
		#	self.ftp = ftplib.FTP(self.hostname)
		#else:
		#	self.ftp = ftplib.FTP_TLS(self.hostname) # 如果在远端，必要加密传输
		self.ftp = ftplib.FTP(self.hostname)
		self.ftp.login(self.username, self.password)
		self.ftp.cwd(self.path)
		self.ftp.retrlines("MLSD", self.cb1)
		self.ftp.quit()
		self.signal_completed.emit(self.remote_attachments)

class RemoteFTPAttachmentUploaderThread(QtCore.QThread):
	signal_completed = QtCore.pyqtSignal(object)
	signal_progress  = QtCore.pyqtSignal(object)
	def __init__(self, x):
		QtCore.QThread.__init__(self)
		self.hostname = x["hostname"]
		self.username = x["username"]
		self.password = x["password"]
		self.path     = x["path"]
		self.file_list = x["file_list"]
		self.remote_filename_list = x["remote_filename_list"]
		
	def run(self):
		# 2016-07-16: 因为某种原因导致了Connection reset by peer，所以先停用SFTP一段时间  
		#if self.hostname == "127.0.0.1" or self.hostname == "10.42.0.1": # 如果只在本机，可以用明文传输
		#	self.ftp = ftplib.FTP(self.hostname)
		#else:
		#	self.ftp = ftplib.FTP_TLS(self.hostname) # 如果在远端，必要加密传输
		self.ftp = ftplib.FTP(self.hostname)
		self.ftp.login(self.username, self.password)
		self.ftp.cwd(self.path)
		for idx in xrange(0, len(self.file_list)):
			fn = self.file_list[idx]; rfn = self.remote_filename_list[idx]
			f = open(fn, "rb")
			result = self.ftp.storbinary(("STOR %s" % rfn), f)
			txt = u"已经上传 %d/%d 个, %s -> %s, %s" % ((idx+1), len(self.file_list), fn, rfn, result)
			# self.plaintext_ftp_upload_status.setPlainText(result)
			self.signal_progress.emit(txt)
			f.close()
		self.ftp.quit()
		txt = u"上传了 %d 个 附件。" % len(self.remote_filename_list)
		
class DiskAnalyzerThread(QtCore.QThread):
	signal_completed = QtCore.pyqtSignal()
	signal_progress  = QtCore.pyqtSignal(object)
	def __init__(self, x):
		QtCore.QThread.__init__(self)
		self.date_begin = x["date_begin"]
		self.date_end   = x["date_end"]
		self.fns = x["folder_names"] # Folder NameS
	def run(self):
		print "Thread runs"
		analyze.g_totalnum = 0
		
		num = 0
		for f in self.fns:
			files = os.listdir(f)
			analyze.g_totalnum += len(os.listdir(f))
			
		n = 0
		for fn in self.fns:
			files = os.listdir(fn)
			for f in files:
				n = n + 1
				sz = "%d / %d" % (n, analyze.g_totalnum)
				self.signal_progress.emit(sz)
				if os.path.isdir(f): continue
				else: 
					full_fn = fn + "/" + f
					
					if self.date_begin is not None:
						if full_fn.endswith(".eml"):
							m = re.match(".*(?P<dt>\d{4}\-\d\d\-\d\d \d{4}).*", full_fn);
							if m:
								x = m.group("dt")
								year = int(x[0:4]); month = int(x[5:7]); day = int(x[8:10]); hour = int(x[11:13]); minute = int(x[13:15])
								us_central = pytz.timezone("US/Central")
								utc = pytz.timezone("UTC")
								naive_datetime = datetime.datetime(year, month, day, hour, minute)
								central_datetime = us_central.localize(naive_datetime)
								if central_datetime < self.date_begin or central_datetime >= self.date_end:
									sys.stdout.write("s")
									continue
									
					
					analyze.AnalyzeOneEmail(full_fn)
		self.signal_completed.emit();
	
class MailFetchThread(QtCore.QThread):
	signal_progress = QtCore.pyqtSignal(object)
	signal_completed = QtCore.pyqtSignal()
	def __init__(self, x):
		QtCore.QThread.__init__(self)
		print "args:", str(x)
		self.server   = x["server"]
		self.account  = x["account"]
		self.password = x["password"]
		self.querydate= x["querydate"]
		self.destination=x["destination"]
	def run(self):
		print "Mail Fetching Thread runs"
		self.M = imaplib.IMAP4_SSL(self.server)
		try:
			rv, data = self.M.login(self.account, self.password)
		except imaplib.IMAP4.error as e:
			print e
			self.signal_progress.emit(str(e))
			print e
			return
		print rv, data
		self.signal_progress.emit(str(data))
		rv, mailboxes = self.M.list()
		if rv == "OK":
			self.signal_progress.emit(str(mailboxes))
			print str(mailboxes)
		MAILBOXES = ["INBOX", "[Gmail]/Spam", "[Gmail]/Important", "[Gmail]/Trash", "[Gmail]/Sent Mail"]
		for i, mb in enumerate(MAILBOXES):
			rv, data = self.M.select(mb)
			if rv == "OK":
				print "Processing mailbox ...", mb
				self.signal_progress.emit("Processing mailbox ... \n")
			else:
				print "Cannot select mailbox", mb
				self.signal_progress.emit("Cannot select mailbox " + mb);
				continue
			rv, data = self.M.search(None, "ON", self.querydate)
			if rv != "OK":
				self.signal_progress.emit("No messages found!")
				self.M.close();
				continue
			blah = data[0].split()
			for x, num in enumerate(blah):
				self.signal_progress.emit(str("Email %d/%d, Mailbox %d/%d" % \
					(x+1, len(blah), (i+1), len(MAILBOXES))))
				
				# 先看标题。如果已经存在了就不下载整封邮件
				# 更新 2016-06-02：对于有的信，如果不全下载（用"(RFC822)"作参数）
				#   就会导致标题乱码。在这种情况下要把整封信都下下来并设定flag_refetched为真
				flag_refetched = False
				rv, data = self.M.fetch(num, '(BODY[HEADER])')
				if rv != "OK":
					print "Error getting message", num
					self.signal_progress.emit("Error getting message " + str(num))
					return
				msg = email.message_from_string(data[0][1])
				subject, coding = analyze.ExtractMySubject(msg["Subject"]);
				if subject is None:
					rv, data = self.M.fetch(num, '(RFC822)')
					print "Unable to decode the header; fetching entire email"
					msg = email.message_from_string(data[0][1])
					subject, coding = analyze.ExtractMySubject(msg["Subject"])
					flag_refetched = True
				tmp,     _      = analyze.ExtractMySubject(msg["From"]);
				date_tuple = email.utils.parsedate_tz(msg['Date'])
				if date_tuple:
					us_central = pytz.timezone("US/Central")
					utc = pytz.timezone("UTC")
					#local_date = datetime.datetime.fromtimestamp(
					#	email.utils.mktime_tz(date_tuple))
					
					# 转换到 UTC、先获得一个 对应着 UTC 的 Naive Datetime Object
					#  然后给这个 Naive Datetime Object 赋上 UTC 时区
					naive_datetime = datetime.datetime.utcfromtimestamp(email.utils.mktime_tz(date_tuple))
					utc_datetime = utc.localize(naive_datetime)
					
					# 然后把 UTC 时区 转换成 US/Centrao 时区
					local_date = utc_datetime.astimezone(us_central)
					sys.stdout.write("LocalTime:%s，US/Central Time:%s " % (\
						msg["Date"], \
						local_date.strftime("%a, %d %b %Y %H:%M:%S")))
				if date_tuple:
					fn = "%s - %s - %s.eml" % ( \
						subject, tmp, local_date.strftime("%Y-%m-%d %H%M"))
				else:
					fn = "%s - %s - Unknown Date.eml" % (\
						subject, tmp)
				fn = fn.replace("/", "_")
				if len(fn) > 100: # 文件名太长了
					fn = fn[:100] + fn[-4:];
				utf8fn = (u"%s/%s" % (self.destination, fn)).encode("utf-8")
				if os.path.exists(utf8fn):
					print "This mail has already been downloaded. skip!"
					continue
					
				is_skip = False;
				if msg["To"] is None: # 2016-06-04 新情况
					print "This message has to recipient. Skipped. (Subject: %s)" % msg["Subject"]
					is_skip = True;
				if msg["To"] is not None:
					if "cssa-l@listserv.lsu.edu" not in msg["To"].lower():
						is_skip = True;
						print "This message header says it's not sent to LSU CSSA Mailing List (%s)" % msg["To"]
				if is_skip: continue
				
				if not flag_refetched:
					rv, data = self.M.fetch(num, "(RFC822)")
				if rv != "OK":
					print "Error getting message", num
					self.signal_progress.emit("Error getting message " + str(num))
					return
				msg = email.message_from_string(data[0][1])
				
				tmp,     _      = analyze.ExtractMySubject(msg["From"]);
				
				try:
					f = open(utf8fn, "w")
				except Exception as e:
					print "Oh! Error opening folder for save. Maybe the destination does not exist?"
					print e
					continue
				gen = email.generator.Generator(f)
				gen.flatten(msg)
				print "Saving email to %s" % fn
				f.close()
			self.M.close();
		print "Done with searching all specified folders!"
		self.signal_completed.emit()

# 站点关闭信息是写在文件里的，所以得要用FTP来取得控制文件


def SetSiteOnlineState(on_or_off, x):
	assert on_or_off == 'on' or on_or_off == 'off'
	hostname = x["hostname"]
	username = x["ftp_uname"]
	password = x["ftp_passwd"]
	remote_config_path = x["ftp_config_path"]
#	if hostname == "127.0.0.1" or hostname == "10.42.0.1": ftp = ftplib.FTP(hostname)
#	else: ftp = ftplib.FTP_TLS(hostname)
	ftp = ftplib.FTP(hostname);
	ftp.login(username, password)
	ftp.cwd(remote_config_path)
	
	FILENAME_IN = '/dev/shm/myconfig.php_in'
	FILENAME_OUT= '/dev/shm/myconfig.php_out'
	
	f = open(FILENAME_IN, 'w')
	ftp.retrbinary('RETR myconfig.php', f.write)
	f.close()
	
	f     = open(FILENAME_IN,  'r')
	f_out = open(FILENAME_OUT, 'w')
	for line in f:
		line = line.strip()
		m = re.match(".*'site_close' => .*", line)
		if m:
			f_out.write("  'site_close' => '%s',\n" % on_or_off)
		else:
			if on_or_off == "off":
				if "site_close_msg" in line:
					f_out.write("  'site_close_msg' => '此BBS正在进行邮件列表至论坛的数据"+
						"更新，更新开始时间是%s。此更新通常用时一分钟左右。请稍候片刻，谢谢！',\n" % 
						datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
				else:
					f_out.write(line + "\n")
			else:
				f_out.write(line + "\n")
	f.close()
	f_out.close()
	
	f = open(FILENAME_OUT, 'rb')
	ftp.storbinary('STOR myconfig.php', f)
	f.close()
	
	ftp.quit()

def do_ReadDB(x):
	hostname = x["hostname"]
	port     = x["port"]
	username = x["username"]
	passwd   = x["pwd"]
	dbname   = x["dbname"]

	# 以下为回传的结果
	max_topic_id = 0; max_comment_id = 0; max_user_id = 0
	max_notification_id = 0
	db_messages = []
	db_topics = []; db_comments = []; db_notifications = []
	db_replies = []
	db_uid_to_email = dict()
	db_email_to_user = dict()
	
	try:
		mydb = MySQLdb.connect(host = hostname, port = port,
			user = username, passwd = passwd, db = dbname,
			charset = "utf8")
	except Exception as e:
		print e
		assert False
		return None
	hdl = mydb.cursor();
	# 1. Fetch all users.
	print "fetch all users"
	hdl.execute("SET @@session.wait_timeout=3600;");
	hdl.execute("SELECT * FROM `stb_users`;");
	result = hdl.fetchall();
	for item in result:
		uid = int(item[0]); nom = item[1]; eml = item[5];
		if max_user_id < uid: max_user_id = uid
		db_uid_to_email[uid] = eml
		u = analyze.User(uid, eml, nom)
		assert uid != -999;
		u.num_topics   = int(item[11])
		u.num_comments = int(item[12])
		if item[17] is None: u.regtime = 0
		else               : u.regtime = int(item[17])
		if item[19] is None: u.lastpost = 0
		else               : u.lastpost = int(item[19])
		db_email_to_user[eml] = u;
	
	# 2. Fetch and count emails per user
	print "fetch ALL TOPICS"
	hdl.execute("SELECT * FROM `stb_topics` ORDER BY ADDTIME ASC;");
	result = hdl.fetchall();
	topicid_to_topic = dict();
	topicid_to_rowhead = dict()
	ret = []
	uid_to_count = dict()
	for item in result:
		if max_topic_id < int(item[0]): max_topic_id = int(item[0])
		uid = int(item[2])
		topic_id = int(item[0])
		if not uid_to_count.has_key(uid): uid_to_count[uid] = 0
		uid_to_count[uid] += 1
		if db_uid_to_email.has_key(uid):
			eml = db_uid_to_email[uid]
			user = db_email_to_user[eml]
		ts = int(item[7])
		cont, att = analyze.ExtractAttachmentHashes(item[6])
		node_id = int(item[1])
		node_name = analyze.NodeIDToNodeName(node_id)
		m = analyze.Message(user, item[4], cont, ts, att, node_id, int(item[17]))
		m.primary_key = topic_id # 差点就没抓住这个BUG。
		m.is_reply = False
		m.last_reply_time = int(item[9])
		ret.append(m)
		topicid_to_topic[item[0]]   = m;
		db_messages.append(m);
	db_topics = ret[:]
		
	# 3. 回复
	hdl.execute("SELECT * FROM `stb_comments`;")
	result = hdl.fetchall();
	for item in result:
		if max_comment_id < item[0]: max_comment_id = item[0]
		uid = int(item[2])
		if not uid_to_count.has_key(uid): uid_to_count[uid] = 0
		uid_to_count[uid] += 1
		if db_uid_to_email.has_key(uid):
			eml = db_uid_to_email[uid]
			user = db_email_to_user[eml]
		ts = int(item[4])
		cont, att = analyze.ExtractAttachmentHashes(item[3])
		m = analyze.Message(user, u"（回复）", cont, ts, att, -999, int(item[5]))
		m.primary_key = int(item[0])
		m.is_reply = True
		
		if not topicid_to_topic.has_key(item[1]): continue

		m.parent = topicid_to_topic[item[1]]
		m.parent.children.append(m)
		if (m.flag & 0x01) == 0x00:
			m.parent_hash = m.parent.getHash()
		db_messages.append(m);
		db_comments.append(m)
	
	# 4. 通知
	hdl.execute("SELECT * FROM `stb_notifications`;")
	result = hdl.fetchall()
	for item in result:
		nid = int(item[0])
		if max_notification_id < nid: max_notification_id = nid;
		topic_id = int(item[1]); 
		if topicid_to_topic.has_key(item[1]): # 有可能帖子删除了
			topic = topicid_to_topic[item[1]] 
			from_uid = int(item[2]); from_user = db_email_to_user[db_uid_to_email[from_uid]]
			to_uid   = int(item[3]); to_user = db_email_to_user[db_uid_to_email[to_uid]]
			ntype    = int(item[4])
			timestamp = int(item[5])
			n = analyze.Notification(nid, topic, from_user, to_user, ntype, timestamp)
			to_user.addNotification(n)
			db_notifications.append(n)
		
	for uid, eml in db_uid_to_email.items():
		if uid_to_count.has_key(uid):	
			cnt = str(uid_to_count[uid])
		else:
			cnt = "Unknown"
		user = db_email_to_user[eml]
		nom = user.name
		
	# 5. Attachment Lookup Table
	hdl.execute("SELECT * FROM `stb_mailattachments`;");
	result = hdl.fetchall()
	remote_att_hash_fn = dict() # Hash to FileName
	for item in result:
		remote_att_hash_fn[item[0]] = item[1]
		
	# 6. Tag的列表与Tag的关系表
	db_tags = dict();
	db_tags_relation = dict();
	hdl.execute("SELECT * FROM `stb_tags`;");
	result = hdl.fetchall()
	for item in result:
		tag_id     = int(item[0]);
		tag_title  = item[1];
		tag_ncount = int(item[2]);
		db_tags[tag_title] = [tag_id, tag_ncount];
	hdl.execute("SELECT * FROM `stb_tags_relation`;");
	result = hdl.fetchall();
	for item in result:
		tag_id   = int(item[0])
		topic_id = int(item[1])
		if not db_tags_relation.has_key(tag_id):
			db_tags_relation[tag_id] = set([])
		db_tags_relation[tag_id].add(topic_id)
			
	return {
		"max_topic_id": max_topic_id,
		"max_comment_id": max_comment_id,
		"max_user_id": max_user_id,
		"max_notification_id": max_notification_id,
		"db_topics": db_topics,
		"db_comments": db_comments,
		"db_messages": db_messages,
		"db_notifications": db_notifications,
		"db_uid_to_email": db_uid_to_email,
		"db_email_to_user": db_email_to_user,
		"attachment_hash_to_filename": remote_att_hash_fn,
		"db_tags": db_tags,
		"db_tags_relation": db_tags_relation,
		"topicid_to_topic": topicid_to_topic
	}


def LoadConfigs():
	global g_configs
	CONF_FILE = "./configs.txt";
	g_configs = do_loadconfigs(CONF_FILE)

g_my_app = None;
g_w = None;
class MyApp(QtGui.QMainWindow, Ui_MainWindow):

	def setInitDate(self):
		# 设为今日日期。
		dt = datetime.datetime.now()
		self.dateedit_fetch.setDate(QtCore.QDate(dt.year, dt.month, dt.day))
		self.UpdateEffectiveDestination()

	def __init__(self):
		global g_configs, g_lastsave
		LoadConfigs()
		QtGui.QMainWindow.__init__(self)
		Ui_MainWindow.__init__(self)
		self.setupUi(self)
		self.disk_messages = [];  self.disk_email_to_user = dict();
		self.disk_new_messages = set([])
		self.db_new_messages   = set([])
		self.disk_new_users = [];
		self.users_lastpost_updated = []; # 有谁更新了「最后发表」
		self.db_messages = [];    self.db_email_to_user = dict();
		self.db_uid_to_email = dict();
		self.db_messages_with_new_nodeid = dict()
		self.local_attachments = [];
		self.remote_attachments = [];
		
		# 通知从DB来比从Disk来要方便一点
		# self.disk_notifications = []; self.db_notifications = [];
		# self.disk_new_notifications = []; self.db_new_notifications = [];
		
		curridx = 0
		for i, x in enumerate(g_configs.keys()):
			self.combobox_preset.addItem(x)
			if g_lastsave.has_key("remote_preset") and\
				g_lastsave["remote_preset"] == x:
				curridx = i
		self.combobox_preset.setCurrentIndex(curridx)
		self.OnComboBoxPresetChanged(g_configs.keys()[curridx])
		
		self.btn_scan.clicked.connect(self.OnScanClicked)
		self.btn_readdb.clicked.connect(self.ReadDB)
		self.btn_computeupdate.clicked.connect(self.GenerateSQLs)
		self.btn_commit.clicked.connect(self.OnUpdateTopicUserClicked)
		self.btn_commit_special.clicked.connect(self.OnUpdateSpecialClicked)
		self.btn_commit.setEnabled(False)
		self.btn_computeupdate.setEnabled(False)
		self.btn_reordertopics.clicked.connect(self.ReorderTopicsByTime)
		self.btn_clearall.clicked.connect(self.ClearTopicsCommentsUsers)
		self.btn_clear_topic_and_cmts.clicked.connect(self.ClearTopicsComments)
		self.connect(self.combobox_preset, QtCore.SIGNAL("currentIndexChanged(const QString&)"),
			self.OnComboBoxPresetChanged)
		self.btn_printhashes.clicked.connect(self.PrintAllHashes)
		self.btn_computestats.clicked.connect(self.RecomputeStats)
		self.btn_fetch.clicked.connect(self.OnFetchClicked)
		self.lineedit_reporoot.textChanged.connect(self.UpdateEffectiveDestination)
		self.dateedit_fetch.dateChanged.connect(self.UpdateEffectiveDestination)
		self.UpdateEffectiveDestination()
		self.btn_refresh_attachments.clicked.connect(self.RefreshAttachments)
		self.btn_delete_attachment_index.clicked.connect(self.DeleteLocalAttachmentIndex)
		self.btn_refresh_remote_attachments.clicked.connect(self.RefreshRemoteAttachments)
		self.btn_upload_attachments.setEnabled(False)
		self.btn_upload_attachments.clicked.connect(self.UploadAttachments)
		self.local_att_hash_fn = dict()  # hash fn 表示 hash and FileName
		self.remote_att_hash_fn = dict()
		self.btn_update_attachment_index.setEnabled(False)
		self.btn_update_attachment_index.clicked.connect(self.UpdateAttachmentIndex)
		self.btn_classify_db_messages.setEnabled(False)
		self.btn_classify_db_messages.clicked.connect(self.ClassifyDBMessages)
		self.btn_update_nodeid.setEnabled(False)
		self.btn_update_nodeid.clicked.connect(self.UpdateNodeIDs)
		self.btn_save_db_new_messages.clicked.connect(self.SaveDBNewMessages)
		self.btn_computenotices.clicked.connect(self.RecomputeNotifications)
		self.btn_match_old_content_with_db.clicked.connect(self.MatchOldContentWithDB)
		self.btn_match_old_content_with_db_writedb.clicked.connect(self.WriteUpgradedContentToDB);
		self.btn_renew_tags.clicked.connect(self.RenewTags);
		self.btn_dump_tag_nodeid.clicked.connect(self.DumpTagNodeID);

		self.m2v_disk = dict() # Mail to View.
		self.m2v_db   = dict() 
		self.u2v_disk = dict() # User to View.
		self.u2v_db   = dict()
		self.a2v_local = dict() # Attachment to View.
		self.a2v_remote = dict()
		self.n2v_db   = dict(); # Notification to View
		self.n2v_disk = dict(); 
		self.max_comment_id = 0; # 2016-02-19:解决“topic_id突然变大很多”这一问题的Duct tape solution。
		self.max_topic_id   = 0;
		self.max_user_id    = 0;
		self.local_new_attachments = [];
		self.lineedit.textChanged.connect(self.OnAnalysisPathChanged)
		
		if g_lastsave.has_key("lineedit_local_repo"):
			x = g_lastsave["lineedit_local_repo"].replace(SEP, "\n")
			self.lineedit.setPlainText(x)
		
		# Tree Widget Operation
		l = [
			QtGui.QTreeWidgetItem(["No UID", "Nobody", "No Subject",
				"No Content", "No Time", "None"])
		]

		ll = QtGui.QTreeWidgetItem(["NoUID1", "Nobody 1", "No Subject 1",
				"No Content 1", "No Time 1", "None"])

		l[0].addChild(ll)
		l[0].setBackgroundColor(0, QtGui.QColor(0x22FF22));
		self.treewidget0.addTopLevelItems(l);
		
		cwd = os.getcwd()
		self.btn_versioninfo.setEnabled(False);
		if cwd.endswith('next/') or cwd.endswith('next'):
			self.btn_versioninfo.setText(u"此为next（下一次更新预定使用）版本。");
			self.btn_versioninfo.setStyleSheet('background-color: rgb(255, 95, 95);')
		else:
			self.btn_versioninfo.setStyleSheet('background-color: rgb(127,127,127);')

	def PrintAllHashes(self):
		print "Messages in Disk:"
		for x in self.disk_messages:
			print ">>>"
			print x.getHash()
		print "Messages in DB:"
		for x in self.db_messages:
			print ">>>"
			print x.getHash()
			

	def IntersectMessages(self, msgs1, msgs2, m2v1, m2v2, new_set_1, new_set_2): # M2V means Message to View
		self.db_messages_with_new_nodeid.clear()
		new_set_1.clear(); new_set_2.clear()
		contents1 = dict()
		intersection = set([])
		common_msgs = set([])
		for m in msgs1:
			contents1[m.getHash()] = m
			
		if len(msgs1) == 1 and len(msgs2) == 1:
			h1 = msgs1[0].getHash(); h2 = msgs2[0].getHash();
			print u"[%s]\nvs\n[%s]\n" % (h1, h2)
			print "h1 == h2:", (h1 == h2)
			if h1 != h2:
				for x in range(0, min(len(h1), len(h2))):
					if h1[x] != h2[x]:
						print "h1[%d] != h2[%d]" % (x, x)
						print h1[x:]
						print "vs"
						print h2[x:]
						break
			
		for m in msgs2:
			key = m.getHash()
			if contents1.has_key(key):
				common_msgs.add(key)
				if m2v2:
					x = m2v2[m]
					SetBackgroundColorQTreeWidgetItem(x, 0xDDDDDD)
				if m2v1:
					m1 = contents1[key]
					if m2v1.has_key(m1):
						x = m2v1[m1]
						SetBackgroundColorQTreeWidgetItem(x, 0xDDDDDD)
						# 在读磁盘文件时，一条信息是没有primary key的
						m1.primary_key = m.primary_key
						if m1.is_reply == False:
							x.setText(1, "tid=%d" % m.primary_key);
						else:
							x.setText(1, "cid=%d" % m.primary_key);
		# Seen in set #1 but not in set #2
		
		for m in msgs1:
			key = m.getHash()
			if key not in common_msgs:
				new_set_1.add(m)
				if m2v1.has_key(m):
					x = m2v1[m]
					SetBackgroundColorQTreeWidgetItem(x, 0x22FF22)
					if m.is_reply == False:
						x.setText(1, u"（需要分配新tid）");
					else:
						x.setText(1, u"（需要分配新cid,parent_tid=%d）" % m.parent.primary_key);

		# Seen in set #2 but not in set #1
		for m in msgs2:
			key = m.getHash()
			if key not in common_msgs:
				if (m.flag & 0x01) == 0: 
					new_set_2.add(m)
				if m2v2.has_key(m):
					x = m2v2[m]
					if (m.flag & 0x01) == 0:
						SetBackgroundColorQTreeWidgetItem(x, 0x2222DD)
					else:
						SetBackgroundColorQTreeWidgetItem(x, 0xCCCCCC)
			else:
				m1 = contents1[m.getHash()]
				if m2v1.has_key(m1):
					x = m2v1[m1]
					x.setText(1, u"（已存在）")
				if m1.node_id != m.node_id:
					self.db_messages_with_new_nodeid[m] = m1.node_id
		
		return intersection

	# 在需要加入新用户时判定重不重复只看email名
	def IntersectUsersAndAssignUID(self, users1, users2, u2v1, u2v2): # U2V means User to View
		self.last_new_uid = -1;
		self.users_lastpost_updated = []
		newusers = []
		emails1 = set([])
		intersect_emls = set([])
		for u in users1.keys():
			emails1.add(u)
		for u in users2.keys():
			if u in emails1:
				intersect_emls.add(u)
				if users2[u].regtime == 0:
					# 如果db侧和disk侧的此用户的注册时间皆空，那就把它置为disk侧的此用户的最后发表时间
					if users1[u].regtime == 0:
						users1[u].regtime = users2[u].regtime = users1[u].lastpost
					else:
						users2[u].regtime = users1[u].regtime
					x = u2v2[users2[u]]
					x.setText(3, analyze.EpochToDateTime(users2[u].regtime).strftime("%a, %d %b %Y %H:%M:%S"))
				if users1[u].regtime == 0:
					if users2[u].regtime == 0:
						users1[u].regtime = users2[u].regtime = users1[u].lastpost
					else:
						users1[u].regtime = users2[u].regtime
		for k, u in users1.items():
			if k in intersect_emls:
				kolor = 0xDDDDDD
				if users2[k].lastpost < u.lastpost:
					kolor = 0x2222FF
					users2[k].updateLastPost(u.lastpost)
					self.users_lastpost_updated.append(users2[k])
			else:
				newusers.append(u)
				u.regtime = u.lastpost

		uid = self.max_user_id + 1
		for x in newusers:
			x.uid = uid;
			self.last_new_uid = uid;
			uid = uid + 1
		print "%d new users" % len(newusers)
		return newusers
		
	# 消除重名
	# 邮件列表允许重名，不允许重复的email
	# 论坛不允许重名，也不允许重复的email
	# 
	# 论坛中不分大小写的。
	#
	def DedupUserName(self, new_users, existing_users):
		allnames = set([])
		for x in existing_users:
			allnames.add(x.name.lower())
		for x in new_users:
			if x.name.lower() in allnames:
				x.dedup_num = 1
				while True:
					if x.getEffectiveName().lower() not in allnames:
						allnames.add(x.getEffectiveName().lower())
						break
					else:
						x.dedup_num += 1
			else:
				allnames.add(x.name.lower())

	def GenerateSQLs(self):
		self.sqlmsg = u""
		self.GenerateSQLForNewTopics()
		self.GenerateSQLForNewUsers()
		self.label_sqlmessages.setText(self.sqlmsg)

	# 假定已经分配了primary key
	def GenerateSQLForNewTopics(self):
		global g_all_posts
#		analyze.ComputePrimaryKeys(self.max_topic_id + 1, self.max_comment_id + 1) # 不用调用analyze中的了。在这里计算primary key。		
		if not (len(self.disk_messages) > 0 and len(self.db_messages) >= 0): return
		allsqls = ""
		num_new_topics = 0; num_new_comments = 0
		tid = self.max_topic_id + 1
		cid = self.max_comment_id + 1
		processed_replies = set([])
		for m in self.disk_new_messages:
			if m.is_reply == True:
				continue
			ts = m.date
			assert m.primary_key != -1
			m.primary_key = tid
			tid += 1
			assert m.sender.uid != -999
			sql = m.toSQL()
			num_new_topics += 1
			allsqls += sql + "\n"
			self.m2v_disk[m].setText(1, u"新tid=%d" % m.primary_key)
			for c in m.children:
				if c not in self.disk_new_messages: continue
				if c in processed_replies: continue
				assert c.is_reply
				assert c.primary_key != -1
				c.primary_key = cid
				self.m2v_disk[c].setText(1, u"新cid=%d" % c.primary_key)
				cid += 1
				assert c.sender.uid != -999
				sql = c.toSQL()
				num_new_comments += 1
				processed_replies.add(c)
				allsqls += sql + "\n"
		# 剩下的回复
		# Make sure every topic touches the last reply
		updated_topics = set([])
		for c in self.disk_new_messages:
			if c in processed_replies: continue
			if c.is_reply == True:
				assert c.primary_key != -1
				assert c.sender.uid != -999
				if c.parent is None:
					print "Dangling Reply.",
					print c.subject,
					print c.content
					continue
				c.primary_key = cid
				cid += 1
				num_new_comments += 1
				allsqls += c.toSQL() + "\n"
				self.m2v_disk[c].setText(1, u"新cid=%d,parent的tid=%d" % (c.primary_key,
					c.parent.primary_key))
				updated_topics.add(c.parent)
				c.parent.updateLastReply(c, c.sender)
				if c.parent not in self.disk_new_messages:
					updated_topics.add(c.parent)
		for t in updated_topics:
			assert t.is_reply == False
			self.m2v_disk[t].setText(1, u"要更新；tid=%d" % t.primary_key)
			allsqls += t.toUpdateLastReplySQL() + "\n"
			
		# 这个计数的移到后面的 RecomputeStats() 里面了
#		allsqls += "UPDATE `stb_nodes` SET `listnum`=%d WHERE 1;" % tid
		
		if (self.last_new_uid != -1):	
			dtnow = datetime.datetime.now()	
			tsnow = int(dtnow.strftime("%s"));
			allsqls += "\nUPDATE `stb_site_stats` SET `value`=" + \
				str(self.last_new_uid) + ", `update_time`=" + \
				str(tsnow) + " WHERE `item`=\"last_uid\"\n";
		
		self.plaintext_sql.setPlainText(allsqls)
		self.sqlmsg += u"%d个新主题，%d个新回复" % (
			num_new_topics, num_new_comments)
		self.btn_commit.setEnabled(True)
		self.g_sql_posts = allsqls

	# Todo: 处理【update】的情况
	def GenerateSQLForNewUsers(self):
		allsqls = ""
		for x in self.disk_new_users:
			assert x.uid != -1
			allsqls += x.toSQL() + "\n"
		self.plaintext_sql_users.setPlainText(allsqls)
		
		self.g_sql_users = allsqls
		self.sqlmsg += u"和 %d 个新用户" % \
			len(self.disk_new_users)
	# 通知应该从DB的Messages来，这样比从Disk来要方便一些

	def OnFetcherProgress(self, sz):
		self.label_fetchermessage.setText(sz)
	
	def OnFetcherCompleted(self):
		self.label_fetchermessage.setText("Done!")
		self.SetMailFetchControlsEnabled(True);

	def OnDiskMessageProgress(self, sz):
		self.label_diskmessages.setText(sz)

	def OnDiskMessageParsed(self):
		analyze.SortAndConstructThreads()
		analyze.SaveAttachmentRepository()
		# Messages here
		tmp = set([])
		for m in analyze.g_allmessages:
			if m in tmp: continue
			if m.is_reply == False:
				tmp.add(m)
				node_id = m.node_id
				node_name = analyze.NodeIDToNodeName(node_id)
				entry = QtGui.QTreeWidgetItem([
					m.sender.name,
					u"（N/A）",
					("%s(%d)" % (node_name, node_id)).decode("utf-8"),
					m.subject, 
					analyze.ContentAndAttachmentsToSQLString(m.content, m.attachments), 
					analyze.EpochToDateTime(m.date).strftime(DATEFMT),
					str(len(m.attachments)),
					m.getOrigin()
				])
				self.m2v_disk[m] = entry;
				for r in m.children:
					tmp.add(r)
					c = QtGui.QTreeWidgetItem([
						r.sender.name, 
						u"（N/A）",
						r.subject,
						u"（回复）",
						analyze.ContentAndAttachmentsToSQLString(r.content, r.attachments),
						analyze.EpochToDateTime(r.date).strftime(DATEFMT),
						str(len(m.attachments)),
						m.getOrigin()
					])
					self.m2v_disk[r] = c;
					entry.addChild(c)
				self.treewidget0.addTopLevelItems([entry]);
			else:
				if m.parent is None:
					analyze.g_dangling_replies.append(m)
				else:
					tmp.add(m)
		self.disk_messages     = analyze.g_allmessages[:]
		self.disk_email_to_user= analyze.g_email_to_user
		self.disk_user_count   = analyze.g_sender_count
		self.label_diskmessages.setText(
			GetMessageSummary(self.disk_messages) +
			GetSendersSummary(self.disk_email_to_user)
		)

		# Senders here
		
		#for eml, user in self.disk_email_to_user.items():
		#	if self.disk_user_count.has_key(eml):
		#		cnt = str(self.disk_user_count[eml])
		#	else:
		#		cnt = "Unknown"
		#	if user.regtime == 0:
		#		regtime_sz = "N/A";
		#	else:
		#		regtime_sz = analyze.EpochToDateTime(user.regtime).strftime("%a, %d %b %Y %H:%M:%S")
		#	entry = QtGui.QTreeWidgetItem([
		#		user.uid,
		#		eml, 
		#		user.name, 
		#		cnt,
		#		regtime_sz,
		#		analyze.EpochToDateTime(user.lastpost).strftime("%a, %d %b %Y %H:%M:%S")
		#	])
		#	self.treewidget_user0.addTopLevelItems([entry])
		#	self.u2v_disk[user] = entry
		
		# 计算需要更新的部分
		# 你可以先读数据库再读硬盘上的文件，也可以先读硬盘上的文件再读数据库
		# 无论你以什么顺序，以下这几行都要执行的DB读出来后变得已知了。
		u_changed_uid = set([])
		
		self.IntersectMessages(self.disk_messages, self.db_messages,
			self.m2v_disk, self.m2v_db, self.disk_new_messages, self.db_new_messages)
		self.db_new_messages_nonmail = []
		for x in self.db_new_messages:
			if x.flag == 0:
				self.db_new_messages_nonmail.append(x)
		self.label_db_new_messages.setText(u"bbs 中有%d个新帖子，其中%d个是非邮件" % ( \
			len(self.db_new_messages), len(self.db_new_messages_nonmail)));
		self.disk_new_users = self.IntersectUsersAndAssignUID(self.disk_email_to_user, self.db_email_to_user,
			self.u2v_disk, self.u2v_db)
		self.DedupUserName(self.disk_new_users, self.db_email_to_user.values())
		for u in self.disk_new_users:
			self.disk_email_to_user[u.email] = u # 更新topics的时候要用到
			self.db_email_to_user[u.email] = u
		for m in self.disk_new_messages: # 把相应的User ID对齐
			if self.db_email_to_user.has_key(m.sender.email):
				u = self.db_email_to_user[m.sender.email]
				m.sender = u
		# 把 DB 中的 用户ID 同步给 磁盘中 读出的 资料上。
		for e, u in self.db_email_to_user.items():
			assert u.uid != -999
			if self.disk_email_to_user.has_key(e):
				u_disk = self.disk_email_to_user[e]
				if u_disk.uid != u.uid:
					u_changed_uid.add(u_disk)
					u_disk.uid = u.uid;
		for m, v in self.m2v_disk.items():
			if m.is_reply == True:
				v.setText(1, "(Parent tid=%d)" % m.parent.primary_key)
				
		new_mask = [] # 有哪些用户是在disk上存在但在db不存在的
		changed_mask = [] # 在db读完后用。表示哪些用户的UID从
		for u in self.disk_email_to_user.values():
			if u in self.disk_new_users: new_mask.append(True)
			else: new_mask.append(False)
			if u in u_changed_uid: changed_mask.append(True)
			else: changed_mask.append(False)
		
		self.treewidget_user0.clear()
		self.do_refreshUsers("disk", self.disk_email_to_user.values(),
			new_mask, changed_mask, self.u2v_disk)

		self.treewidget0.setEnabled(True)
		self.treewidget_user0.setEnabled(True)
		self.btn_scan.setEnabled(True)

	def OnScanClicked(self):
		for m in analyze.g_allmessages:
			m.children = []
		analyze.LoadAttachmentRepository();
		analyze.g_allmessages = []
		analyze.g_email_to_user = dict()
		analyze.g_allusers = []
		analyze.g_sender_count.clear()
		self.m2v_disk.clear()
		self.disk_messages = []
		self.treewidget0.clear()
		self.treewidget_user0.clear();
		analyze.g_totalnum = 0

		# 不准再按
		self.treewidget0.setEnabled(False)
		self.treewidget_user0.setEnabled(False);
		self.btn_scan.setEnabled(False)

		fns = unicode(self.lineedit.toPlainText()).split("\n")
		args = {"folder_names": fns, "date_begin": None, "date_end": None}
		self.analyzer = DiskAnalyzerThread(args)
		self.analyzer.signal_completed.connect(self.OnDiskMessageParsed)
		self.analyzer.signal_progress.connect(self.OnDiskMessageProgress)
		self.analyzer.start()

	def SetMailFetchControlsEnabled(self, is_enabled):
		self.btn_fetch.setEnabled(is_enabled)
		self.dateedit_fetch.setEnabled(is_enabled);
		self.lineedit_fetchpassword.setEnabled(is_enabled);
		self.lineedit_fetchserver.setEnabled(is_enabled);
		self.lineedit_account.setEnabled(is_enabled);
		self.lineedit_reporoot.setEnabled(is_enabled);

	def OnFetchClicked(self):
		args = dict()
		args["server"] = str(self.lineedit_fetchserver.text())
		args["password"] = str(self.lineedit_fetchpassword.text())
		dt = self.dateedit_fetch.date()
		d = dt.day(); m = dt.month(); y = dt.year();
		months = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
		args["querydate"] = "%02d-%s-%04d" % (d, months[m-1], y)
		args["account"] = str(self.lineedit_account.text())
		args["destination"] = unicode(self.label_destination.text())

		self.SetMailFetchControlsEnabled(False);
		self.fetcher = MailFetchThread(args)
		self.fetcher.signal_progress.connect(self.OnFetcherProgress)
		self.fetcher.signal_completed.connect(self.OnFetcherCompleted)
		self.fetcher.start()

	# 按一下以后就开始从DB中读取东西。
	def ReadDB(self):
		self.max_topic_id = 0  ;   max_topic_id = 0;
		self.max_comment_id = 0; max_comment_id = 0;
		self.max_user_id =  0  ;    max_user_id = 0;
		self.btn_commit.setEnabled(False)
		self.m2v_db.clear()
		self.db_messages = []
		uid_to_count = dict()
		self.db_uid_to_email = dict()
		self.db_email_to_user = dict()
		self.u2v_db = dict()
		self.treewidget1.clear()
		self.treewidget_user1.clear()
		hostname = str(self.lineedit_hostname.text())
		port     = int(self.lineedit_port.text())
		username = str(self.lineedit_username.text())
		pwd      = str(self.lineedit_password.text())
		dbname   = str(self.lineedit_dbname.text())
		mydb = None
		
		self.label_dbmessages.setText("Working ...");
		try:
			mydb = MySQLdb.connect(host = hostname, port = port,
				user = username, passwd = pwd, db = dbname,
				charset = "utf8")
		except Exception as e:
			print "Hohoho"
			self.label_dbmessages.setText(str(e))
			print e
			return

		hdl = mydb.cursor();
		
		x = dict()
		x["hostname"] = str(self.lineedit_hostname.text())
		x["port"]     = int(self.lineedit_port.text())
		x["username"] = str(self.lineedit_username.text())
		x["pwd"]      = str(self.lineedit_password.text())
		x["dbname"]   = str(self.lineedit_dbname.text())
		self.label_dbmessages.setText("Working ...");
		
		dbret = do_ReadDB(x)
		self.db_uid_to_email = dbret["db_uid_to_email"]
		self.db_email_to_user = dbret["db_email_to_user"]
		self.max_user_id = dbret["max_user_id"]
		self.max_notification_id = dbret["max_notification_id"]
		max_comment_id = dbret["max_comment_id"]
		max_topic_id = dbret["max_topic_id"]
		self.db_topics = dbret["db_topics"]
		self.db_messages = dbret["db_messages"]
		self.db_comments = dbret["db_comments"]
		self.db_notifications = dbret["db_notifications"]
		self.remote_att_hash_fn = dbret["attachment_hash_to_filename"]
		self.db_tags = dbret["db_tags"]; self.db_tags_relation = dbret["db_tags_relation"]
		self.topicid_to_topic = dbret["topicid_to_topic"]
		
		topicid_to_topic = dict()
		topicid_to_rowhead = dict()
		for m in self.db_topics:
			node_id = m.node_id
			node_name = analyze.NodeIDToNodeName(node_id)
			row = QtGui.QTreeWidgetItem([
				m.sender.name,
				str(m.primary_key),
				("%s(%d)" % (node_name, node_id)).decode("utf-8"),
				m.subject,
				m.content,
				analyze.EpochToDateTime(m.date).strftime(DATEFMT), # Long
				str(len(m.attachments)),
				m.getOrigin()
			])
			self.m2v_db[m] = row
			topicid_to_topic[m.primary_key] = m
			topicid_to_rowhead[m.primary_key] = row
			self.treewidget1.addTopLevelItems([row])
			
		# 3. 回复	
		for m in self.db_comments:
			child = QtGui.QTreeWidgetItem([
				m.sender.name,
				str(m.primary_key),
				u"（回复）",
				m.subject,
				m.content,
				analyze.EpochToDateTime(m.date).strftime(DATEFMT), # Long
				str(len(m.attachments)),
				m.getOrigin()
			])
			self.m2v_db[m] = child
			topicid_to_rowhead[m.parent.primary_key].addChild(child)
			
		# 4. 未读通知
		print "%d notifications" % len(self.db_notifications)
		for n in self.db_notifications:
			v = QtGui.QTreeWidgetItem([
				unicode(str(n.nid)),
				u"%d (%s)" % (n.topic.primary_key, n.topic.subject[:20]),
				u"%d (%s)" % (n.from_user.uid, n.from_user.email),
				u"%d (%s)" % (n.to_user.uid,   n.to_user.email),
				unicode(str(n.ntype)),
				analyze.EpochToDateTime(n.timestamp).strftime(DATEFMT)
			])
			self.n2v_db[n] = v;
			self.treewidget_remote_notification.addTopLevelItems([v])
			
		# 5. 用户
		for uid, eml in self.db_uid_to_email.items():
			if uid_to_count.has_key(uid):	
				cnt = str(uid_to_count[uid])
			else:
				cnt = "Unknown"
			user = self.db_email_to_user[eml]
			nom = user.name
			if user.regtime == 0:
				regtime_sz = "N/A"
			else: 
				regtime_sz = analyze.EpochToDateTime(user.regtime).strftime("%a, %d %b %Y %H:%M:%S")
			row = QtGui.QTreeWidgetItem([
				str(user.uid),
				eml,
				nom,
				cnt,
				regtime_sz,
				analyze.EpochToDateTime(user.lastpost).strftime("%a, %d %b %Y %H:%M:%S")
			])
			self.treewidget_user1.addTopLevelItems([row])
			self.u2v_db[user] = row
			
		if len(self.disk_messages) > 0:
			self.IntersectMessages(self.disk_messages, self.db_messages,
				self.m2v_disk, self.m2v_db, self.disk_new_messages, self.db_new_messages);
			self.db_new_messages_nonmail = []
			for x in self.db_new_messages:
				if x.flag == 0:
					self.db_new_messages_nonmail.append(x)
			self.label_db_new_messages.setText(u"bbs中有%d个新帖子，其中%d个为非邮件" % \
				(len(self.db_new_messages), len(self.db_new_messages_nonmail)));
			# 对于disk侧和db侧共有的用户，先清除disk侧的注册时间
			for k, v in self.disk_email_to_user.items():
				v.regtime = 0
			self.disk_new_users = self.IntersectUsersAndAssignUID(self.disk_email_to_user, self.db_email_to_user,
				self.u2v_disk, self.u2v_db)
			self.DedupUserName(self.disk_new_users, self.db_email_to_user.values())
			for u in self.disk_new_users:
				self.disk_email_to_user[u.email] = u # 更新topics的时候要用到
				self.db_email_to_user[u.email] = u
			for m in self.disk_new_messages:
				u = self.db_email_to_user[m.sender.email]
				m.sender = u
			# 把 DB 中的 用户ID 同步给 磁盘中 读出的 资料上。
			for e, u in self.db_email_to_user.items():
				assert u.uid != -999
				if self.disk_email_to_user.has_key(e):
					self.disk_email_to_user[e].uid = u.uid;
			#self.IntersectNotifications(self.disk_notifications, self.db_notifications,
			#	self.n2v_disk, self.n2v_db, self.disk_new_notifications, self.db_new_notifications)


		# 下一个能用的ID应该是当前最高ID加上1
		self.max_comment_id = max_comment_id;
		self.max_topic_id   = max_topic_id;
		analyze.g_stb_topic_id   = max_topic_id   + 1
		analyze.g_stb_comment_id = max_comment_id + 1
		self.btn_computeupdate.setEnabled(True);
		self.label_dbmessages.setText(GetMessageSummary(self.db_messages))
		self.btn_reordertopics.setEnabled(True)
		
		self.btn_classify_db_messages.setEnabled(True)
		
		# 读入 附件的索引
		self.treewidget_remote_attachment_index.clear()
		for h, fn in self.remote_att_hash_fn.items():
			entry = QtGui.QTreeWidgetItem([h, fn])
			self.treewidget_remote_attachment_index.addTopLevelItems([entry])
		self.IntersectAttachmentIndex();
		
		self.IntersectTags()
	
	# 更新“今日主题”、“昨日主题”、”话题总数“、”回复数“
	def RecomputeStats(self):
		hostname = str(self.lineedit_hostname.text())
		port     = int(self.lineedit_port.text())
		username = str(self.lineedit_username.text())
		pwd      = str(self.lineedit_password.text())
		dbname   = str(self.lineedit_dbname.text())
		mydb = None
		
		try:
			mydb = MySQLdb.connect(host = hostname, port = port,
				user = username, passwd = pwd, db = dbname,
				charset = "utf8")
		except Exception as e:
			self.label_dbmessages.setText(str(e))
			print e
			return
		hdl = mydb.cursor();
		# 取得「今日话题数」，从今天的0点0分0秒（含）开始算。
		# 以下命令与时区有关的。换一个时区结果就会不同。
		dtnow = datetime.datetime.now()
		dt = datetime.datetime(dtnow.year, dtnow.month, dtnow.day)
		ts = int(dt.strftime("%s"))
		tsnow = int(dtnow.strftime("%s"))
		
		hdl.execute("SELECT COUNT(*) FROM `stb_topics` WHERE `addtime` >= %d;" % ts);
		result = hdl.fetchall();
		item = result[0];
		today_topics = nrows = item[0];
		print "Topics since >= Local time %s (Unix timestamp %d): %d" % \
			(str(dt), ts, nrows)
		
		# 取得「昨日话题数」
		dt_yesterday = dt + datetime.timedelta(days=-1)
		ts_yesterday = int(dt_yesterday.strftime("%s"))
		hdl.execute(("SELECT COUNT(*) FROM `stb_topics` WHERE `addtime` >= %d AND" +\
			" `addtime` < %d;") % (ts_yesterday, ts))
		result = hdl.fetchall()
		item = result[0]
		yesterday_topics = nrows = item[0]
		print "Topics yesterday = [%s,%s) = %d" % (str(dt_yesterday), str(dt),
			nrows)
		
		# 取得「话题总数」
		hdl.execute("SELECT COUNT(*) FROM `stb_topics`;")
		result = hdl.fetchall()
		item = result[0]
		total_topics = nrows = item[0]
		print "Count of all topics: %d" % nrows
		
		# 取得「回复数」
		hdl.execute("SELECT COUNT(*) FROM `stb_comments`;")
		result = hdl.fetchall()
		item = result[0]
		total_comments = nrows = item[0]
		print "Count of all comments: %d" % nrows
		
		# User count
		hdl.execute("SELECT COUNT(*) FROM `stb_users`;")
		result = hdl.fetchall()
		item = result[0]
		total_users = nrows = item[0]
		print "Count of all comments: %d" % nrows
		
		allsqls = ""
		keys = ["total_users", "today_topics", "yesterday_topics", \
			"total_topics", "total_comments"];
		values = [total_users, today_topics, yesterday_topics,
			total_topics, total_comments];
			
		for i in range(0, len(keys)):
			sql = ("UPDATE `stb_site_stats` SET " + \
				"`value`=%d, `update_time`=%d " + \
				"WHERE `item`=\"%s\";\n") % \
				(values[i], tsnow, keys[i]);
			allsqls += sql;
		
		ntc = dict() # Node Topic Count
		for m in self.db_messages:
			nid = m.node_id
			if nid == -999:
				assert m.is_reply
				continue
			else:
				if not ntc.has_key(nid):
					ntc[nid] = 0
				ntc[nid] += 1
		sql += "UPDATE stb_nodes SET listnum=CASE "
		for k, v in ntc.items():
			sql = sql + "WHEN node_id=%d THEN %d " % (k, v)
		sql = sql + "ELSE 0 END;"
		allsqls += sql
		
		self.plaintext_sql_special.setPlainText(allsqls)
		self.btn_commit_special.setEnabled(True);
		self.g_sql_special = allsqls;
	
	def ReorderTopicsByTime(self):
		self.btn_commit_special.setEnabled(True)
		if len(self.db_messages) < 1: return
		self.db_messages = sorted(self.db_messages, 
			key = lambda x : x.last_reply_time, reverse = False) # 已经转换成时间戳了。
		order = 0
		sql = "UPDATE stb_topics SET ord = CASE "
		for m in self.db_messages:
			if m.is_reply == False:
				m.order = order;
				order += 1;
				#sql = sql + m.toUpdateOrdSQL() + "\n"
				sql = sql + "WHEN topic_id = %d THEN %d " % (m.primary_key, m.order)
		sql = sql + "ELSE ord END;"
		self.plaintext_sql_special.setPlainText(sql)
		self.btn_commit_special.setEnabled(True);
		self.g_sql_special = sql;
	
	def OnUpdateTopicUserClicked(self):
		self.btn_commit.setEnabled(False)
		self.WriteToDB(self.g_sql_posts + "\n" + self.g_sql_users)
	
	def OnUpdateSpecialClicked(self):
		self.btn_commit_special.setEnabled(False)
		self.WriteToDB(self.g_sql_special);
	
	def ClearTopicsCommentsUsers(self):
		self.btn_commit_special.setEnabled(True)
		self.g_sql_special = "delete from `stb_topics` where 1;\n" +\
			"delete from `stb_comments` where 1;\n" +\
			"delete from `stb_users` where uid>2;\n" +\
			"delete from `stb_notifications` where 1;\n"
		self.plaintext_sql_special.setPlainText(self.g_sql_special);
		
	def ClearTopicsComments(self):
		self.btn_commit_special.setEnabled(True)
		self.g_sql_special = "delete from `stb_topics` where 1;\n" +\
			"delete from `stb_comments` where 1;\n" +\
			"delete from `stb_notifications` where 1;\n"
		self.plaintext_sql_special.setPlainText(self.g_sql_special);
	
	def WriteToDB(self, sql):
#		global g_sql_posts, g_sql_users
#		sql = g_sql_posts + "\n" + g_sql_users
		hostname = str(self.lineedit_hostname.text())
		port     = int(self.lineedit_port.text())
		username = str(self.lineedit_username.text())
		pwd      = str(self.lineedit_password.text())
		dbname   = str(self.lineedit_dbname.text())
		mydb = MySQLdb.connect(host = hostname, port = port,
			user = username, passwd = pwd, db = dbname,
			charset = "utf8")
		hdl = mydb.cursor();
		for s in sql.split("\n"):
			if s != "":
				hdl.execute(s);
				num_row_affected = mydb.affected_rows();
				print "%d rows affected" % num_row_affected
		mydb.commit();
		hdl.close();
		print "Done!"

	def OnComboBoxPresetChanged(self, text):
		global g_lastsave
		self.btn_computeupdate.setEnabled(False);
		self.btn_commit.setEnabled(False)
		conf = g_configs[str(text)]
		self.lineedit_hostname.setText(conf["hostname"]);
		self.lineedit_port.setText(conf["mysql_port"])
		self.lineedit_username.setText(conf["mysql_uname"]);
		self.lineedit_password.setText(conf["mysql_passwd"]);
		self.lineedit_dbname.setText(conf["mysql_dbname"])
		self.lineedit_ftp_uname.setText(conf["ftp_uname"])
		self.lineedit_ftp_passwd.setText(conf["ftp_passwd"])
		self.lineedit_ftp_path.setText(conf["ftp_path"])
		g_lastsave["remote_preset"] = text 
	 
	def UpdateEffectiveDestination(self):
		dt = self.dateedit_fetch.date()
		d = dt.day(); m = dt.month(); y = dt.year();
		md = "%04d%02d" % (y, m)
		x = unicode(self.lineedit_reporoot.text())
		if x == '': return
		idx = len(x) - 1
		while x[idx] == '/': idx -= 1
		x = x[0:idx+1] + "/" + md
		self.label_destination.setText(x)
		
	def RefreshAttachments(self):
		self.a2v_local = dict()
		self.local_attachments = []
		idx_loc = str(self.lineedit_attachment_list_location.text())
		if not os.path.exists(idx_loc):
			self.plaintext_attachment_info.setText("Error: The specified attachment list file does not exist.");
			return
		local_remote = str(self.lineedit_attachment_local_remote.text())
		if not os.path.exists(local_remote):
			self.plaintext_attachment_info.setText("Error: The specified attachment local remote directory does not exist.");
			return
		
		self.lineedit_attachment_list_location.setEnabled(False)
		self.lineedit_attachment_local_remote.setEnabled(False)
		self.btn_refresh_attachments.setEnabled(False)
		self.treewidget_local_att.setEnabled(False)
		args = dict()
		args["index_location"] = idx_loc
		args["local_remote"] = local_remote
		self.att_refresher = AttachmentManagerThread(args)
		self.att_refresher.signal_completed.connect(self.OnAttachmentUpdateCompleted)
		self.att_refresher.start()
		
	def DeleteLocalAttachmentIndex(self):
		idx_loc = str(self.lineedit_attachment_list_location.text())
		if not os.path.exists(idx_loc):
			self.plaintext_attachment_info.setPlainText(u"本地附件还不存在，没什么好删除的。");
			return
		else:
			os.remove(idx_loc)
			print "本地附件index被删除了。"
		
	def RefreshRemoteAttachments(self):
		self.a2v_remote = dict()
		self.remote_attachments = []
		self.treewidget_remote_att.clear()
		args = dict()
		args["hostname"] = str(self.lineedit_hostname.text())
		args["username"] = str(self.lineedit_ftp_uname.text())
		args["password"] = str(self.lineedit_ftp_passwd.text())
		args["path"]     = str(self.lineedit_ftp_path.text())
		self.lineedit_ftp_uname.setEnabled(False);
		self.lineedit_ftp_passwd.setEnabled(False);
		self.lineedit_ftp_path.setEnabled(False);
		self.treewidget_remote_att.setEnabled(False)
		self.remote_att_refresher = RemoteFTPAttachmentListThread(args)
		self.remote_att_refresher.signal_completed.connect(self.OnRemoteAttachmentUpdateCompleted)
		self.remote_att_refresher.start()
	
	def OnAttachmentUpdateCompleted(self, summary, attachments):
		x = summary
		txt = u"%d个附件，其中%d个可以缩小。" % (x["num_files"], x["has_small"])
		txt += u"原尺寸／缩小后总大小%.2fMiB／%.2fMiB\n" % (x["bytes_orig"] / 1048576.0, x["bytes_effective"] / 1048576.0)
		txt += u"其中缩小版占据的空间为%.2fMiB。\n" % (x["bytes_small"] / 1048576.0)
		if x["missing_orig"] > 0: txt += u"这些附件中有 %d 个原尺寸的找不到了。" % x["missing_orig"]
		else: txt += u"原尺寸附件看起来都正常。"
		if x["missing_small"] > 0: txt += u"这些附件中有 %d 个缩小版的找不到了。" % x["missing_small"]
		else: txt += u"缩小版的附件看起来都正常。"
		txt += u"\n其中有 %d 个有对应的远端文件名。" % x["has_remote_path"]
		self.plaintext_attachment_info.setPlainText(txt);
		self.local_attachments = attachments[:]
		self.local_attachments = sorted(self.local_attachments, key = lambda x:x.datetime)
		
		# 把附件状态写到View里去
		# 在这里还顺带检查文件
		self.a2v_local = dict()
		self.treewidget_local_att.clear()
		self.local_att_hash_fn.clear()
		for a in self.local_attachments:
			p = a.path
			if not os.path.exists(p): s1 = "（文件不存在）"
			else: 
				size1 = os.path.getsize(p)
				#s1 = "%.2f MiB" % (size1/1048576.0)
				s1 = str(size1)
			tp = a.thumbpath
			if tp == "[none]":
				s2 = u"(100%%)(不需缩小)"
			else:
				if not os.path.exists(tp): s2 = "(文件不存在)"
				else:
					size2 = os.path.getsize(tp)
					#s2 = u"(%d%%)（%.2f MiB）" % ((size2*100-size1)/size1+1, size2/1048576.0)
					s2 = "(%d%%) %d" % ((size2*100-size1)/size1+1, size2)
			entry = QtGui.QTreeWidgetItem([
				a.filehash,
				analyze.EpochToDateTime(a.datetime).strftime("%a, %d %b %Y %H:%M:%S"),
				s1, s2,
				a.remote_filename
			])
			if a.remote_filename != "[none]":
				self.local_att_hash_fn[a.filehash] = a.remote_filename
			self.a2v_local[a] = entry
			self.treewidget_local_att.addTopLevelItems([entry])
		self.treewidget_local_att.setEnabled(True)
		self.btn_refresh_attachments.setEnabled(True)
		self.lineedit_attachment_list_location.setEnabled(True)
		self.lineedit_attachment_local_remote.setEnabled(True)
		self.btn_refresh_remote_attachments.setEnabled(True);
		self.IntersectAttachments()
		self.IntersectAttachmentIndex()
		
	def OnRemoteAttachmentUpdateCompleted(self, ra):
		self.remote_attachments = sorted(ra[:], key=lambda x:x.filename)
		self.a2v_remote = dict()
		for a in self.remote_attachments:
			entry = QtGui.QTreeWidgetItem([
				a.filename, 
				str(a.size), 
				a.mtime.strftime("%a, %d %b %Y %H:%M:%S")
			])
			self.treewidget_remote_att.addTopLevelItems([entry])
			self.a2v_remote[a] = entry
		self.lineedit_ftp_uname.setEnabled(True);
		self.lineedit_ftp_passwd.setEnabled(True);
		self.lineedit_ftp_path.setEnabled(True);
		self.btn_refresh_remote_attachments.setEnabled(True);
		self.treewidget_remote_att.setEnabled(True)
		self.IntersectAttachments()
		
	def IntersectAttachments(self):
		self.btn_upload_attachments.setEnabled(False)
		self.local_new_attachments = []
		fn_size_to_a_0 = dict() # 本地的远端文件名和大小
		fn_size_to_a_1 = dict() # 远端的远端文件名和大小
		
		for a in self.a2v_local.keys():
			fn_size_to_a_0[(a.remote_filename, a.effective_size)] = a;
		for a in self.a2v_remote.keys():
			fn_size_to_a_1[(a.filename, a.size)] = a
		
		num_uploadable = 0
		for f_s in fn_size_to_a_0.keys():
			a = fn_size_to_a_0[f_s]
			v_local = self.a2v_local[a]
			SetBackgroundColorQTreeWidgetItem(v_local, 0xFFFFFF)
			if f_s in fn_size_to_a_1.keys():
				SetBackgroundColorQTreeWidgetItem(v_local, 0xDDDDDD)
				a_remote = fn_size_to_a_1[f_s]
				v_remote = self.a2v_remote[a_remote]
				SetBackgroundColorQTreeWidgetItem(v_remote, 0xDDDDDD)
			else:
				self.local_new_attachments.append(a)
				if a.remote_filename == "[none]": c = 0xFF2222
				else: 
					c=0x00FF00; num_uploadable += 1
				SetBackgroundColorQTreeWidgetItem(v_local, c)
		for f_s in fn_size_to_a_1.keys():
			a = fn_size_to_a_1[f_s]
			v_remote = self.a2v_remote[a]
			SetBackgroundColorQTreeWidgetItem(v_remote, 0xFFFFFF)
			if f_s in fn_size_to_a_0.keys():
				SetBackgroundColorQTreeWidgetItem(v_remote, 0xDDDDDD)
			else:
				SetBackgroundColorQTreeWidgetItem(v_remote, 0x00FF00)
		# 2016-05-29:
		#  在这里就能知道哪些附件只在本地、哪些附件只在远端、哪些附件两边皆有
		num_na = len(self.local_new_attachments)
		txt = u"在本地有%d个新附件，其中的%d个可以上传，%d个有问题尚不能上传。" % (num_na, num_uploadable, num_na - num_uploadable) 
		self.plaintext_ftp_upload_status.setPlainText(txt)
		if num_na > 0:
			self.btn_upload_attachments.setEnabled(True)
			
	def OnAttachmentUploadProgress(self, txt):
		self.plaintext_ftp_upload_status.setPlainText(txt)
	
	def OnAttachmentUploadCompleted(self, txt):
		self.plaintext_ftp_upload_status.setPlainText(txt)
		self.btn_upload_attachments.setEnabled(True)
		self.btn_refresh_remote_attachments.setEnabled(True)
	
	def UploadAttachments(self):
		if len(self.local_new_attachments) <= 0: return
		file_list = []; remote_filename_list = []
		for a in self.local_new_attachments:
			if a.remote_filename == "[none]":
				# 此文件因某些原因不能读入，比如错误的文件名编码之类的
				continue
			if a.thumbpath == "[none]":
				eff_fn = a.path
			else:
				eff_fn = a.thumbpath
			file_list.append(eff_fn)
			remote_filename_list.append(a.remote_filename)
		
		hname = str(self.lineedit_hostname.text())
		uname = str(self.lineedit_ftp_uname.text())
		passwd= str(self.lineedit_ftp_passwd.text())
		ftppath= str(self.lineedit_ftp_path.text())
		
		args = dict()
		args["hostname"] = hname
		args["username"] = uname
		args["password"] = passwd
		args["path"] = ftppath
		args["file_list"] = file_list
		args["remote_filename_list"] = remote_filename_list
		
		self.btn_upload_attachments.setEnabled(False)
		self.btn_refresh_remote_attachments.setEnabled(False)
		self.attachment_uploader_thread = RemoteFTPAttachmentUploaderThread(args)
		self.attachment_uploader_thread.signal_completed.connect(self.OnAttachmentUploadCompleted)
		self.attachment_uploader_thread.signal_progress.connect(self.OnAttachmentUploadProgress)
		self.attachment_uploader_thread.start()
	
	# 这里还尚未处理“文件的hash没变但是文件名突然变了”的情况，
	#  但愿那种情况不会发生。
	def IntersectAttachmentIndex(self):
		self.g_sql_att_hash = ""
		new_att_hashes = set([])
		for hf in self.local_att_hash_fn:
			if not self.remote_att_hash_fn.has_key(hf):
				new_att_hashes.add(hf)
		sql = ""
		idx = 0
		for h in new_att_hashes:
			if idx > 0: sql = sql + ","
			else: sql = sql + "INSERT IGNORE INTO `stb_mailattachments` VALUES " 
			sql = sql + "(\"%s\", \"%s\") " % (h, self.local_att_hash_fn[h])
			idx += 1
		sql = sql + ";"
		self.g_sql_att_hash = sql
		self.plaintext_attachment_index_sql.setPlainText(sql)
		txt = u"看起来有 %d 个新的附件索引条目的样子。" % len(new_att_hashes)
		self.plaintext_attachment_index_status.setPlainText(txt);
		if sql != "":
			self.btn_update_attachment_index.setEnabled(True);
		
	def UpdateAttachmentIndex(self):
		self.btn_update_attachment_index.setEnabled(False)
		if self.g_sql_att_hash != ";":
			self.WriteToDB(self.g_sql_att_hash);
		self.plaintext_attachment_index_status.setPlainText("Done");
	
	def ClassifyDBMessages(self):
		nodeid_uncategorized = analyze.NodeNameToNodeID("未归类")
		is_uncategorized_only = self.cb_only_uncategorized.isChecked()
		sql = ""
		nnid = 0
		for idx, m in enumerate(self.db_messages):
			sys.stdout.write("\r%d / %d     " % (idx+1, len(self.db_messages)))
			sys.stdout.flush()
			if is_uncategorized_only:
				if m.node_id != nodeid_uncategorized:
					continue
			soup = BeautifulSoup(m.content, "html.parser")
			parsed = soup.get_text().strip()
			new_nodeid = analyze.Classify(m.subject, parsed)
			if new_nodeid != m.node_id:
				if sql == "":
					sql = "UPDATE stb_topics SET node_id = CASE"
				sql = sql + " WHEN topic_id = %d THEN %d" % (m.primary_key, new_nodeid)
				nnid = nnid + 1
		sql = sql + " ELSE node_id END; "
		print
		self.plaintext_nodeid_sql.setPlainText(sql)
		self.plaintext_attachment_nodeid_status.setPlainText(u"有%d个主题的Node ID发生了改变。" % nnid)
		self.g_sql_update_nodeid = sql
		self.btn_update_nodeid.setEnabled(True)
	
	def UpdateNodeIDs(self):
		if self.g_sql_update_nodeid is not None:
			self.WriteToDB(self.g_sql_update_nodeid);
		self.plaintext_attachment_nodeid_status.setPlainText(u"Done，请重新读db并再更新一下statistics")
		self.btn_update_nodeid.setEnabled(False)

	def OnAnalysisPathChanged(self):
		global g_lastsave, SEP
		x = self.lineedit.toPlainText()
		g_lastsave["lineedit_local_repo"] = x.replace("\n", SEP)
		
	def SaveDBNewMessages(self):
		local_mail_repo_root = str(self.lineedit.toPlainText())
		for x in self.db_new_messages_nonmail:
			fn = x.getFileName()
			full_path = "%s/%s" % (local_mail_repo_root, fn) 
			f = open(full_path, "w")
			x.dumpToPickle(f)
			f.close()
			print "db_new_message -> %s" % full_path
		print "Saved new db msgs to disk!"
		
	def IntersectNotifications(self, notifs1, notifs2, n2v1, n2v2, newset1, newset2):
		hashes1 = set([])
		common_hashes = set([])
		for x in xrange(0, len(newset1)): newset1.pop()
		for x in xrange(0, len(newset2)): newset2.pop()
		
		for n in notifs1:
			hashes1.add(n.getHash())
		for n in notifs2:
			h = n.getHash()
			if h in hashes1:
				common_hashes.add(h)
		
		for n in notifs1:
			if not n.getHash() in common_hashes:
				newset1.append(n)
				v = n2v1[n]
				SetBackgroundColorQTreeWidgetItem(v, 0x33FF33)
			else: SetBackgroundColorQTreeWidgetItem(v, 0xCCCCCC)
		for n in notifs2:
			if not n.getHash() in common_hashes:
				newset2.append(n)
				v = n2v2[n]
				SetBackgroundColorQTreeWidgetItem(v, 0x33FF33)
			else: SetBackgroundColorQTreeWidgetItem(v, 0xCCCCCC)
	
	def RecomputeNotifications(self):
		computed_notifs = []
		diff_set = []
		hashes2 = set([])
		user_to_numnew = dict()
		
		for n in self.db_notifications:
			hashes2.add(n.getHash())
			
		for m in self.db_messages:
			if m.is_reply == False:
				for c in m.children:
					n = analyze.Notification(-999, m, c.sender, m.sender, 1, c.date)
					computed_notifs.append(n)
					if not n.getHash() in hashes2:
						diff_set.append(n)
		
		print "%d db_messages" % len(self.db_messages)
		print "Has %d, computed %d, need to add %d notifications" % ( \
			len(self.db_notifications), len(computed_notifs), len(diff_set))
		
		allsqls = ""
		if len(diff_set) > 0:
			nid = self.max_notification_id
			for n in diff_set:
				nid = nid + 1
				n.nid = nid
				allsqls += n.toSQL() + "\n"
				
			for n in computed_notifs:
				to_email = n.to_user.email
				u = self.db_email_to_user[to_email]
				if n.ntype != 0:
					if not user_to_numnew.has_key(u):
						user_to_numnew[u] = 0
					user_to_numnew[u] += 1
					
			if len(user_to_numnew) > 0:
				allsqls += "UPDATE `stb_users` SET notices = CASE "
				for u, n in user_to_numnew.items():
					allsqls += "WHEN uid=%d THEN %d " % (u.uid, n)
				allsqls += "ELSE notices END"	
		self.plaintext_sql_special.setPlainText(allsqls)
		self.btn_commit_special.setEnabled(True);
		self.g_sql_special = allsqls;
		
	def do_refreshUsers(self, disk_or_db, user_list, new_mask, changed_mask, u2v):
		if disk_or_db == "disk": the_view = self.treewidget_user0
		elif disk_or_db == "db": the_view = self.treewidget_user1
		else: 
			print "Do not know which User QTreeWidget to update"
			return
		for i, u in enumerate(user_list):
			str_num = "%d/%d" % (u.num_topics, u.num_comments)
			if u.regtime == 0: str_rt = "N/A"
			else: str_rt = analyze.EpochToDateTime(u.regtime).strftime(DATEFMT)
			str_lp = analyze.EpochToDateTime(u.lastpost).strftime(DATEFMT)
			entry = QtGui.QTreeWidgetItem([
				str(u.uid), 
				u.email, 
				u.name, 
				str_num, 
				str_rt,
				str_lp
			])
			the_view.addTopLevelItems([entry])
			if new_mask[i] == True: 
				SetBackgroundColorQTreeWidgetItem(entry, 0x33CC33)
			if changed_mask[i] == True:
				entry.setBackgroundColor(0, QtGui.QColor(0x3333CC))
			u2v[u] = entry
	
	def MatchOldContentWithDB(self):
		sql_t = ""; sql_c = ""; sql_t1 = ""; sql_c1 = "";
		disk_matched = dict()
		key_to_dbpost = dict() # Key: (sender.email, is_reply, date)
		
		for x in self.db_messages:
			key_to_dbpost[(x.sender.email, x.is_reply, x.date)] = x
			
		num_t = 0; num_c = 0;
		for x in self.disk_messages:
			if hasattr(x, 'old_content'):
				k = (x.sender.email, x.is_reply, x.date)
				if k in key_to_dbpost.keys():
					x_db = key_to_dbpost[k] 
					if x.getHash() != x_db.getHash() or x.flag != x_db.flag:
						if x_db.is_reply:
							print "Comment ID=%d" % x_db.primary_key
						else:
							print "Topic ID=%d" % x_db.primary_key
						print x.getHash()
						print x_db.getHash()
						print " "
						disk_matched[x] = x_db
						if x_db.is_reply == True: num_c += 1
						else: num_t += 1
		
		if num_t > 0:
			sql_t = "UPDATE `stb_topics` SET content = CASE "
			sql_t1= "UPDATE `stb_topics` SET flag = CASE "
			flag = 3;
			if len(x.attachments) > 0: flag |= 4;
			for x, x_db in disk_matched.items():
				if x_db.is_reply == False:
					sql_t = sql_t + "WHEN `topic_id`=%d THEN '%s' " % ( \
						x_db.primary_key, analyze.ContentAndAttachmentsToSQLString(x.content, x.attachments))
					sql_t1 = sql_t1 + "WHEN `topic_id`=%d THEN %d " % ( \
						x_db.primary_key, flag)
			sql_t = sql_t + "ELSE content END;"
			sql_t1 = sql_t1 + "ELSE flag END;"
		
		if num_c > 0:
			sql_c = "UPDATE `stb_comments` SET content = CASE "
			sql_c1= "UPDATE `stb_comments` SET flag = CASE "
			flat = 3;
			if len(x.attachments) > 0: flag |= 4
			for x, x_db in disk_matched.items():
				if x_db.is_reply == True:
					sql_c = sql_c + "WHEN `id`=%d THEN '%s' " % ( \
						x_db.primary_key, analyze.ContentAndAttachmentsToSQLString(x.content, x.attachments))
					sql_c1= sql_c1+ "WHEN `id`=%d THEN %d " % ( \
						x_db.primary_key, flag)
			sql_c = sql_c + "ELSE content END;"
			sql_c1 = sql_c1 + "ELSE flag END;"
					
		self.sql_upgrade_db = sql_t + "\n" + sql_t1 + "\n" + sql_c + "\n" + sql_c1
		self.plaintext_upgrade_content_sql.setPlainText(self.sql_upgrade_db)
		print "%d/%d topics/comments matched and are eligible for upgrading." % (\
			num_t, num_c)
		
	def WriteUpgradedContentToDB(self):
		if self.sql_upgrade_db == None:
			print u"先要比较一下旧版数据与DB中的数据、确认有可以更新内容的帖子后才能按这个。"
			return
		else:
			self.WriteToDB(self.sql_upgrade_db);
			print "Done"
			self.sql_upgrade_db = None
			
	def IntersectTags(self):
		self.treewidget_tags.clear();
		for t, id_and_nc in self.db_tags.items():
			if self.db_tags_relation.has_key(id_and_nc[0]):
				occ = len(self.db_tags_relation[id_and_nc[0]])
			else: occ = 0
			s = "%d / %d" % (id_and_nc[1], occ)
			x = QtGui.QTreeWidgetItem([t, str(id_and_nc[0]), s])
			if id_and_nc[1] != occ:
				SetBackgroundColorQTreeWidgetItem(x, 0xEE9999)
			self.treewidget_tags.addTopLevelItems([x])
			
	def RenewTags(self):
		x = str(self.lineedit_renewtag_topicids.text());
		if x.lower() == "all":
			tids = self.topicid_to_topic.keys()
		else:
			tids = [int(xx) for xx in x.split(",")]
		all_keywords = set([])
		if len(self.db_tags) < 1: max_kwid = 0
		else: max_kwid = max([x[0] for x in self.db_tags.values()])
		kwfreqs = dict()
		updated_tids = set([])
		new_tr_entries = []
		
		for tid in tids:
			assert self.topicid_to_topic.has_key(tid)
			m = self.topicid_to_topic[tid]
			keywords = jieba.analyse.textrank(m.subject + m.content)
			if (m.keywords is None): m.keywords = set([])
			
			print "Extracted KW for TID %d: %s" % (tid, ",".join(keywords))
			for k in keywords:
				if k in m.keywords: continue
				else:
					m.keywords.add(k)
					if k in self.db_tags.keys():
						k_id = self.db_tags[k][0]
						if self.db_tags_relation.has_key(k_id):
							if tid in self.db_tags_relation[k_id]:
								continue
					new_tr_entries.append([k, tid])
					updated_tids.add(tid)
					all_keywords.add(k)
					if kwfreqs.has_key(k) == False:
						kwfreqs[k] = 0
					kwfreqs[k] += 1
		
		# Overall new tags
		new_keywords = dict()
		old_keywords = dict() # Frequency Change
		currid = max_kwid + 1
		for k in all_keywords:
			if self.db_tags.has_key(k) == False:
				new_keywords[k] = [currid, kwfreqs[k]]
				currid += 1
				
		if len(new_keywords) > 0:
			sql_new_keywords = "INSERT INTO `stb_tags` (`tag_id`, `tag_title`, `topics`) VALUES "
			idx = 0
			for k, v in new_keywords.items():
				if idx > 0: sql_new_keywords += ", "
				sql_new_keywords += "('%d', '%s', '%d')" % (v[0], k, v[1])
				idx += 1
			sql_new_keywords += ";"
		else:
			sql_new_keywords = ""
		print sql_new_keywords
		
		# Tag-to-topic entries
		if len(new_tr_entries) > 0:
			sql_new_tr_entries = "INSERT INTO `stb_tags_relation` (`tag_id`, `topic_id`) VALUES "
			idx = 0
			for x in new_tr_entries:
				k = x[0]
				if k in new_keywords:
					k_id = new_keywords[k][0]
				else:
					k_id = self.db_tags[k][0]
				if idx > 0: sql_new_tr_entries += ","
				sql_new_tr_entries += "('%d', '%d')" % (k_id, x[1])
				idx += 1
			sql_new_tr_entries += ";"
		else:
			sql_new_tr_entries = ""
		print sql_new_tr_entries
		
		# Update tags on the topic side
		if len(updated_tids) > 0:
			sql_update_tag_topic_side = "UPDATE `stb_topics` SET `keywords` = CASE"
			for tid in updated_tids:
				assert self.topicid_to_topic.has_key(tid)
				m = self.topicid_to_topic[tid]
				sql_update_tag_topic_side += " WHEN `topic_id`='%d' THEN '%s'" % ( \
					tid, ",".join(m.keywords))
			sql_update_tag_topic_side += " ELSE keywords END;"
		else:
			sql_update_tag_topic_side = ""
		self.plaintext_sql_special.setPlainText(sql_update_tag_topic_side);
		print sql_update_tag_topic_side
		
	def DumpTagNodeID(self):
		fn = "tags_to_nodeid.txt"
		f_out = codecs.open(fn, "w", encoding="utf-8");
		x = str(self.lineedit_renewtag_topicids.text());
		if x.lower() == "all": tids = self.topicid_to_topic.keys()
		else: tids = [int(xx) for xx in x.split(",")]
		print " "
		n = 0
		is_ignore_uncategorized = self.cb_ignore_uncategorized.isChecked()
		for idx, tid in enumerate(tids):
			sys.stdout.write("%d / %d                   \r" % (idx+1, len(tids)))
			assert self.topicid_to_topic.has_key(tid)
			m = self.topicid_to_topic[tid]
			if is_ignore_uncategorized and analyze.NodeIDToNodeName(m.node_id)=="未归类" : continue
			keywords = jieba.analyse.textrank(m.subject + m.content)
			if (m.keywords is None): m.keywords = set([])
			titlecut = jieba.cut(m.subject)
			titlecut1= jieba.cut(m.subject, cut_all=True)
			f_out.write(u"%d, %d, [%s], [%s]" % (tid, m.node_id, "/".join(titlecut), "/".join(titlecut1)))
			f_out.write("\n");
			n += 1
		print "\nOK! %d data points. File written to %s             " % (n, fn)
		f_out.close()
	
def ParseCmdArgs(argv1):
	global g_configs, SEP
	parsed_args = dict()
	home = os.environ["HOME"]
	parsed_args["local_mail_repo_root"] = home + "/Documents/lsu/cssa/mailbackup/"
	parsed_args["attachment_index_location"] = home + "/Documents/lsu/cssa/mailbackup/attachments.txt"
	for x in argv1:
		if '=' in x:
			xx = x.split('=')
			if xx[0].lower() == "remote": 
				if g_configs.has_key(xx[1]):
					for k, v in g_configs[xx[1]].items():
						parsed_args[k] = v
				else:
					print "Oh! Please give a valid ``remote'' parameter (%s)." % "|".join([x for x in g_configs.keys()])
					exit(1)
			if xx[0].lower() in ["date", "datefrom", "dateto"]:
				m1 = re.match("(?P<year>\d{4})(?P<month>\d{2})(?P<day>\d{2})", xx[1])
				if not m1:
					print "Oh! Please enter a valid date. Format: YYYYMMDD"
					exit(1)
				else:
					y = int(m1.group("year"))
					if y < 2000 or y > 2038:
						print "Year must be between 2000 and 2038."
						exit(1)
					m = int(m1.group("month"))
					d = int(m1.group("day"))
					dt = datetime.datetime(y, m, d)
					us_central = pytz.timezone("US/Central")
					parsed_args[xx[0]] = us_central.localize(dt)
			if xx[0].lower() == "monthrepo":
				parsed_args["monthrepo"] = xx[1].split(SEP)
	return parsed_args

# 临时方案，不优雅
def IntersectMessagesNoGUI(msgs1, msgs2, new_set_1, new_set_2):
	new_set_1.clear()
	contents1 = dict()
	intersection = set([])
	common_msgs = set([])
	for m in msgs1:
		contents1[m.getHash()] = m
	for m in msgs2:
		key = m.getHash()
		if contents1.has_key(key):
			common_msgs.add(key)
			# 在读磁盘信息时，需要把其primary key与db中的primary key统一起来
			contents1[key].primary_key = m.primary_key
	for m in msgs1:
		key = m.getHash()
		if key not in common_msgs:
			new_set_1.add(m)
	for m in msgs2:
		key = m.getHash()
		if key not in common_msgs:
			if (m.flag & 0x01) == 0:
				new_set_2.add(m)
	return intersection
	
def IntersectUsersAndAssignUIDNoGUI(max_user_id, users1, users2):
	last_new_uid = -1
	newusers = []
	emails1 = set([])
	intersect_emls = set([])
	users_lastpost_updated = []
	for u in users1.keys():
		emails1.add(u)
	for u in users2.keys():
		if u in emails1:
			intersect_emls.add(u)
			if users2[u].regtime == 0:
				if users1[u].regtime == 0:
					users1[u].regtime = users2[u].regtime = users1[u].firstpost
				else:
					users2[u].regtime = users1[u].regtime
			if users1[u].regtime == 0:
				if users2[u].regtime == 0:
					users1[u].regtime = users2[u].regtime = users1[u].firstpost
				else:
					users1[u].regtime = users2[u].regtime
	for k, u in users1.items():
		if k in intersect_emls: 
			if users2[k].lastpost < u.lastpost:
				users_lastpost_updated.append(users2[k])
		else:
			u.regtime = u.firstpost
			newusers.append(u)
	uid = max_user_id + 1
	for x in newusers:
		x.uid = uid;
		last_new_uid = uid;
		uid = uid + 1
	print "%d new users" % len(newusers)
	return newusers, last_new_uid, users_lastpost_updated

def DedupUserNameNoGUI(new_users, existing_users):
	allnames = set([])
	for x in existing_users:
		allnames.add(x.name.lower())
	for x in new_users:
		if x.name.lower() in allnames:
			x.dedup_num = 1
			while True:
				if x.getEffectiveName().lower() not in allnames:
					allnames.add(x.getEffectiveName().lower())
					break
				else:
					x.dedup_num += 1
		else:
			allnames.add(x.name.lower())
			
def WriteToDBNoGUI(sql, x):
	hostname = x["hostname"]
	port     = x["port"]
	username = x["username"]
	pwd      = x["pwd"]
	dbname   = x["dbname"]
	mydb = MySQLdb.connect(host = hostname, port = port,
		user = username, passwd = pwd, db = dbname,
		charset = "utf8")
	hdl = mydb.cursor();
	hdl.execute("SET @@LOCAL.wait_timeout=800;");
	for s in sql.split("\n"):
		if s != "":
			hdl.execute(s);
	mydb.commit();
	hdl.close();
	print "DB Operations Done!"

def IntersectAttachmentIndexNoGUI(local_att_hash_fn, remote_att_hash_fn):
	sql_att_hash = ""
	new_att_hashes = set([])
	for hf in local_att_hash_fn:
		if not remote_att_hash_fn.has_key(hf):
			new_att_hashes.add(hf)
	sql = ""
	idx = 0
	for h in new_att_hashes:
		if idx > 0:  sql = sql + ","
		else: sql = sql + "INSERT IGNORE INTO `stb_mailattachments` VALUES " 
		sql = sql + "(\"%s\", \"%s\") " % (h, local_att_hash_fn[h])
		idx += 1
	sql = sql + ";"
	sql_att_hash = sql
	return new_att_hashes, sql_att_hash
	
def IntersectAttachmentsNoGUI(local_attachments, remote_attachments):
	local_new_attachments = []
	fn_size_to_a_0 = dict() # 本地的远端文件名和大小
	fn_size_to_a_1 = dict() # 远端的远端文件名和大小
	for a in local_attachments:
		fn_size_to_a_0[(a.remote_filename, a.effective_size)] = a;
	for a in remote_attachments:
		fn_size_to_a_1[(a.filename, a.size)] = a
	num_uploadable = 0
	for f_s in fn_size_to_a_0.keys():
		a = fn_size_to_a_0[f_s]
		if f_s not in fn_size_to_a_1.keys():
			local_new_attachments.append(a)
	num_na = len(local_new_attachments)
	return local_new_attachments

def OnAttachmentUploadProgressNoGUI(x):
	print x

def LoadLastSave():
	global g_lastsave
	x = "./last_run_config.txt"
	if os.path.exists(x):
		g_lastsave = do_loadconfigs(x)["lastsave"]
	
def SaveLastSave():
	global g_lastsave
	f = open("./last_run_config.txt", "w")
	f.write("[lastsave]\n")
	for k, v in g_lastsave.items():
		f.write("%s=%s\n" % (k, v))
	f.close()

if __name__ == "__main__":
	LoadConfigs()
	if len(sys.argv) >= 2 and sys.argv[1] == "--nogui":
		MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
		parsed_args = ParseCmdArgs(sys.argv)
		#if False: #sys.argv[2] == "ftptest":
		#	SetSiteOnlineState('off', parsed_args)
		#	exit(0);
		if sys.argv[2] == "fetch":
			print "【fetch 从邮件服务器取邮件。】"
			
			if parsed_args.has_key("date"):
				all_dt = [parsed_args["date"]]
			elif parsed_args.has_key("datefrom"):
				if parsed_args.has_key("dateto"):
					all_dt = []
					d0 = parsed_args["datefrom"]
					d1 = parsed_args["dateto"]
					if d0 > d1:
						print "dateto must be later than datefrom."
						exit(1)
					d = d0
					while True:
						if d > d1: break
						us_central = pytz.timezone("US/Central")
						d_temp = us_central.localize(datetime.datetime(d.year, d.month, d.day))
						all_dt.append(d_temp)
						d = d_temp + datetime.timedelta(days=1)
				else:
					print "Must have a 'dateto' with a 'datefrom'"
					exit(1)
			else:
				dt_now = datetime.datetime.now()
				dt_yesterday = dt_now + datetime.timedelta(days=-1)
				all_dt = [dt_now, dt_yesterday] 
			
			for i, dt in enumerate(all_dt):
				print "正在取第 %d/%d 天的信" % ((i+1), len(all_dt))
				if parsed_args.has_key("date"):
					dt = parsed_args["date"]
					print "Fetching: %s" % str(dt)
				args = dict()
				args["server"] = g_configs["CSSAOfficialMail"]["server"]
				args["password"] = g_configs["CSSAOfficialMail"]["password"]
				args["account"] = g_configs["CSSAOfficialMail"]["account"]
				args["querydate"] = "%02d-%s-%04d" % (dt.day, MONTHS[dt.month-1], dt.year)
				year_month = "%04d%02d" % (dt.year, dt.month)
				args["destination"] = parsed_args["local_mail_repo_root"] + "/" + year_month
				fetcher = MailFetchThread(args)
				fetcher.run()
			
			
			exit(0)
		if sys.argv[2] == "miniupdate":
			if not parsed_args.has_key("hostname"):
				print "Must specify remote host name using ``remote'' arg!"
				exit(1)
				
			if not (parsed_args.has_key("datefrom") and parsed_args.has_key("dateto") and parsed_args.has_key("monthrepo")): 
				us_central = pytz.timezone("US/Central")
				dt = datetime.datetime.now() # 时区是本地时间
				dt_today = us_central.localize(datetime.datetime(dt.year, dt.month, dt.day))
				delta_1day = datetime.timedelta(days=1)
				print "将把本地时间的%d年%d月%d日的信件&帖子同步到远端服务器 (%s)" % (dt.year, dt.month, dt.day, parsed_args["hostname"])
				
				dt_yesterday = dt_today - delta_1day
				dt_14days_ago = dt_today - 14 * delta_1day
				dt_today_end = dt_today + delta_1day
				year_month = "%04d%02d" % (dt_today.year, dt_today.month)
				year_month_prev = "%04d%02d" % (dt_yesterday.year, dt_yesterday.month)
				year_month_14days_ago = "%04d%02d" % (dt_14days_ago.year, dt_14days_ago.month)
				month_repo = parsed_args["local_mail_repo_root"] + "/" + year_month
				month_repo_prev = parsed_args["local_mail_repo_root"] + "/" + year_month_prev
				month_repo_14days_ago = parsed_args["local_mail_repo_root"] + "/" + year_month_14days_ago
				fns = [month_repo]
				for x in [month_repo_14days_ago, month_repo_prev]:
					if x not in fns: fns.append(x)
				dt_begin = dt_14days_ago
				assert os.path.exists(month_repo)
				
			else:
				dt_yesterday = parsed_args["datefrom"]
				dt_today_end = parsed_args["dateto"]
				print "将把本地时间的 [%d年%d月%d日, %d年%d月%d日] （包含头尾）的信件&帖子&(其回复=>主帖皆处理此期间的)回复同步到远端服务器 (%s)" % (dt_yesterday.year, dt_yesterday.month, dt_yesterday.day, dt_today_end.year, dt_today_end.month, dt_today_end.day, parsed_args["hostname"]) 
				fns = parsed_args["monthrepo"] # fns means folder names
				dt_begin = dt_yesterday
			
			# Analyze Local
			analyze.LoadAttachmentRepository()
			print "需要解析的文件夹有 %d 个" % len(fns)
			for fn in fns: print " ",fn
			print "需要解析的邮件的日期范围为 [%s, %s)" % (dt_begin.strftime("%a, %d %b %Y %H:%M:%S"), dt_today_end.strftime("%a, %d %b %Y %H:%M:%S"))
			args = {"folder_names": fns, "date_begin": dt_begin, "date_end": dt_today_end}
			analyzer_thread = DiskAnalyzerThread(args)
			analyzer_thread.run()
			
			analyze.SortAndConstructThreads()
			analyze.SaveAttachmentRepository()
			
			# txbegin
			SetSiteOnlineState("off", parsed_args);
			tick = datetime.datetime.now()
			
			# Read DB
			readdb_args = dict()
			readdb_args["hostname"] = parsed_args["hostname"]
			readdb_args["port"] = int(parsed_args["mysql_port"])
			readdb_args["username"] = parsed_args["mysql_uname"]
			readdb_args["pwd"] = parsed_args["mysql_passwd"]
			readdb_args["dbname"] = parsed_args["mysql_dbname"]
			
			dbret = do_ReadDB(readdb_args)
			max_user_id = dbret["max_user_id"]
			max_topic_id = dbret["max_topic_id"]
			max_comment_id = dbret["max_comment_id"]
			db_email_to_user = dbret["db_email_to_user"]
			db_messages = dbret["db_messages"]
			db_notifications = dbret["db_notifications"]
			remote_att_hash_fn = dbret["attachment_hash_to_filename"]
			
			
			# Copy from OnDiskMessageParsed
			tmp = set([])
			for m in analyze.g_allmessages:
				if m in tmp: continue
				if m.is_reply == False:
					tmp.add(m)
					for r in m.children:
						tmp.add(r)
				else:
					if m.parent is None:
						analyze.g_dangling_replies.append(m)
			
			disk_messages = analyze.g_allmessages[:]
			disk_email_to_user = analyze.g_email_to_user
			
				
			# Compute new topics and replies
			disk_new_messages = set([])
			db_new_messages   = set([])
			intersection = IntersectMessagesNoGUI(disk_messages, db_messages, disk_new_messages, db_new_messages)
			
			# Compute new users
			disk_new_users, last_new_uid, users_lastpost_updated = IntersectUsersAndAssignUIDNoGUI(max_user_id,
				disk_email_to_user, db_email_to_user)
			DedupUserNameNoGUI(disk_new_users, db_email_to_user.values())
			for u in disk_new_users:
				disk_email_to_user[u.email] = u
				db_email_to_user[u.email]   = u
			for e, u in db_email_to_user.items():
				assert u.uid != -999
				if disk_email_to_user.has_key(e):
					disk_email_to_user[e].uid = u.uid
					
			db_new_messages_nonmail = []
			for x in db_new_messages:
				if x.flag == 0:
					db_new_messages_nonmail.append(x)
			
			print "BBS中有%d个本地没有的帖子，其中%d个是非邮件的新帖子" % (len(db_new_messages), len(db_new_messages_nonmail))
			for x in db_new_messages_nonmail:
				fn = x.getFileName()
				dt_x = analyze.EpochToDateTime(x.date)
				dir_x = parsed_args["local_mail_repo_root"] + "/" + "%04d%02d" % (dt_x.year, dt_x.month)
				assert os.path.exists(dir_x)
				full_fn = "%s/%s" % (dir_x, fn)
				f = open(full_fn, "w")
				x.dumpToPickle(f)
				f.close()
				print "   %s" % full_fn
			# 因为存在磁盘侧的pickles没有parent的信息，只有sender的信息
			for m in disk_new_messages:
				if db_email_to_user.has_key(m.sender.email):
					u = db_email_to_user[m.sender.email]
					m.sender = u
			# 把本地的 用户的ID 刷新为 远端的用户ID
			for e, u in db_email_to_user.items():
				assert u.uid != -999
				if disk_email_to_user.has_key(e):
					disk_email_to_user[e].uid = u.uid
			
			###### Copied from GenerateSQLForNewTopics
			allsqls = ""
			tid = max_topic_id + 1
			cid = max_comment_id + 1
			num_new_topics = 0
			num_new_comments = 0
			processed_replies = set([])
			for m in disk_new_messages:
				if m.is_reply == True: continue
				ts = m.date
				assert m.primary_key != -1
				m.primary_key = tid
				tid += 1
				assert m.sender.uid != -999
				sql = m.toSQL()
				num_new_topics += 1
				allsqls += sql + "\n"
				for c in m.children:
					if c not in disk_new_messages: continue
					if c in processed_replies: continue
					assert c.is_reply
					assert c.primary_key != -1
					c.primary_key = cid
					cid += 1
					assert c.sender.uid != -999
					sql = c.toSQL()
					num_new_comments += 1
					processed_replies.add(c)
					allsqls += sql + "\n"
			updated_topics = set([])
			for c in disk_new_messages:
				if c in processed_replies: continue
				if c.is_reply == True:
					assert c.primary_key != -1
					assert c.sender.uid != -999
					if c.parent is None:
						print "Dangling Reply.",
						print c.subject,
						print c.content
						continue
					c.primary_key = cid
					cid += 1
					num_new_comments += 1
					allsqls += c.toSQL() + "\n"
					updated_topics.add(c.parent)
					c.parent.updateLastReply(c, c.sender)
					if c.parent not in disk_new_messages:
						updated_topics.add(c.parent)
			for t in updated_topics:
				assert t.is_reply == False
				allsqls += t.toUpdateLastReplySQL() + "\n"
			if (last_new_uid != -1):	
				dtnow = datetime.datetime.now()	
				tsnow = int(dtnow.strftime("%s"));
				allsqls += "\nUPDATE `stb_site_stats` SET `value`=" + \
					str(last_new_uid) + ", `update_time`=" + \
					str(tsnow) + " WHERE `item`=\"last_uid\"\n";
			######
			
			###### Copied from GenerateSQLForNewUsers
			for x in disk_new_users:
				assert x.uid != -1
				allsqls += x.toSQL() + '\n'
			
			###### Attachment Index
			analyze.g_attachmentmanager.LoadFromFile(parsed_args["attachment_index_location"]);
			summary = analyze.g_attachmentmanager.ComputeSummary()
			analyze.g_attachmentmanager.ComputeRemoteFileNames()
			attachments = analyze.g_attachmentmanager.attachments.values()
			local_att_hash_fn = dict()
			for a in attachments:
				if a.remote_filename != "[none]":
					local_att_hash_fn[a.filehash] = a.remote_filename
			new_att_hashes, sql_att_hash = IntersectAttachmentIndexNoGUI(local_att_hash_fn, remote_att_hash_fn)
			if sql_att_hash != ';':
				allsqls = allsqls + sql_att_hash
				
			if len(users_lastpost_updated) > 0:
				sql = "\nUPDATE stb_users SET lastpost = CASE "
				for u in users_lastpost_updated:
					sql = sql + "WHEN uid = %d THEN %d " % (u.uid, u.lastpost)
				sql = sql + "ELSE lastpost END;"
				allsqls += sql
			
			print "# of users with updated lastpost: %d" % len(users_lastpost_updated)
			
			# txcommit
			print u"执行SQL操作中... len(allsqls)=%d." % len(allsqls)
			try:
				WriteToDBNoGUI(allsqls, readdb_args)
			except Exception as e:
				print "@@@@@@@@@@@@@@@@@@@ Hey guys we got some big error!!!!!! @@@@@"
				print e
				print "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
				#exit(1)
				#pdb.set_trace()
			SetSiteOnlineState("on", parsed_args);
			tock = datetime.datetime.now()
			dt = tock - tick
			seconds = dt.seconds + dt.microseconds / 1000000.0
			print u"本次更新所需站点关闭时间为 %.2f 秒。" % seconds
			
			###### Compare attachment File
			args = dict()
			args["hostname"] = parsed_args["hostname"]
			args["username"] = parsed_args["ftp_uname"]
			args["password"] = parsed_args["ftp_passwd"]
			args["path"] = parsed_args["ftp_path"]
			ftp_list_thd = RemoteFTPAttachmentListThread(args)
			ftp_list_thd.run()
			remote_attachments = ftp_list_thd.remote_attachments
			local_new_attachments = IntersectAttachmentsNoGUI(attachments, remote_attachments)
			
			###### Upload the attachments
			file_list = []; remote_filename_list = []
			for a in local_new_attachments:
				if a.remote_filename == "[none]":
					# 此文件因某些原因不能读入，比如错误的文件名编码之类的
					continue
				if a.thumbpath == "[none]":
					eff_fn = a.path
				else:
					eff_fn = a.thumbpath
				file_list.append(eff_fn)
				remote_filename_list.append(a.remote_filename)
			
			args["file_list"] = file_list
			args["remote_filename_list"] = remote_filename_list
			
			print u"%d个本地新附件" % len(local_new_attachments)
			print u"%d个新附件索引条目" % len(new_att_hashes)
			print u"%d个新主题，%d个新回复" % (num_new_topics, num_new_comments)
			print u"%d个新用户" % len(disk_new_users)
			print u"%d个用户的最后发表时间更新了" % len(users_lastpost_updated)
			
			print u"执行FTP上传任务中..."
			uploader_thd = RemoteFTPAttachmentUploaderThread(args)
			uploader_thd.signal_progress.connect(OnAttachmentUploadProgressNoGUI)
			uploader_thd.run()
			print "Done!"
			
			exit(0)
		elif sys.argv[2] == "recomputestats": # 也同时重排
			if not parsed_args.has_key("hostname"):
				print "Must specify a remote host!"
				exit(1)
			print "刷新统计信息并且重新排序..."
			readdb_args = dict()
			readdb_args["hostname"] = parsed_args["hostname"]
			readdb_args["port"] = int(parsed_args["mysql_port"])
			readdb_args["username"] = parsed_args["mysql_uname"]
			readdb_args["pwd"] = parsed_args["mysql_passwd"]
			readdb_args["dbname"] = parsed_args["mysql_dbname"]
			dbret = do_ReadDB(readdb_args)
			db_messages = dbret["db_messages"]
			db_notifications = dbret["db_notifications"]
			max_notification_id = dbret["max_notification_id"]
			db_email_to_user = dbret["db_email_to_user"]
			
			##### Copied from RecomputeStats
			hostname = parsed_args["hostname"]
			port     = int(parsed_args["mysql_port"])
			username = parsed_args["mysql_uname"]
			pwd      = parsed_args["mysql_passwd"]
			dbname   = parsed_args["mysql_dbname"]
			mydb = None
			print "Connect"
			try:
				mydb = MySQLdb.connect(host = hostname, port = port,
					user = username, passwd = pwd, db = dbname,
					charset = "utf8")
			except Exception as e:
				print e
				assert False
			hdl = mydb.cursor();
			print "set timeout"
			# 取得「今日话题数」，从本地时间（US/Central）的今天的0点0分0秒（含）开始算。
			# 以下命令与时区有关的。换一个时区结果就会不同。
			central = pytz.timezone("US/Central")
			utc     = pytz.timezone("UTC")
			utc_now_naive = datetime.datetime.utcnow()
			utc_now_aware = utc.localize(utc_now_naive)
			central_now_aware = utc_now_aware.astimezone(central)
			central_daybegin_aware = central.localize(datetime.datetime( \
				central_now_aware.year, central_now_aware.month, \
				central_now_aware.day ))
			utc_zero_aware = utc.localize(datetime.datetime(1970, 1, 1))
			ts = (central_daybegin_aware - utc_zero_aware).total_seconds()
			tsnow = (utc_now_aware - utc_zero_aware).total_seconds()
			
			print "stb_topics"
			hdl.execute("SELECT COUNT(*) FROM `stb_topics` WHERE `addtime` >= %d;" % ts);
			result = hdl.fetchall();
			item = result[0];
			today_topics = nrows = item[0];
			print "Topics since >= Local time %s (Unix timestamp %d): %d" % \
				(str(central_daybegin_aware), ts, nrows)
			
			# 取得「昨日话题数」
			print "Yesterday's stb_topics"
			dt_yesterday = central_daybegin_aware + datetime.timedelta(days=-1)
			ts_yesterday = (dt_yesterday - utc_zero_aware).total_seconds()
			hdl.execute(("SELECT COUNT(*) FROM `stb_topics` WHERE `addtime` >= %d AND" +\
				" `addtime` < %d;") % (ts_yesterday, ts))
			result = hdl.fetchall()
			item = result[0]
			yesterday_topics = nrows = item[0]
			print "Topics yesterday = [%s,%s) = %d" % (str(dt_yesterday), str(central_daybegin_aware),
				nrows)
			
			# 取得「话题总数」
			print "count of stb_topics"
			hdl.execute("SELECT COUNT(*) FROM `stb_topics`;")
			result = hdl.fetchall()
			item = result[0]
			total_topics = nrows = item[0]
			print "Count of all topics: %d" % nrows
			
			# 取得「回复数」
			print "count of stb_comments"
			hdl.execute("SELECT COUNT(*) FROM `stb_comments`;")
			result = hdl.fetchall()
			item = result[0]
			total_comments = nrows = item[0]
			print "Count of all comments: %d" % nrows
			
			# User count
			print "count of stb_users"
			hdl.execute("SELECT COUNT(*) FROM `stb_users`;")
			result = hdl.fetchall()
			item = result[0]
			total_users = nrows = item[0]
			print "Count of all comments: %d" % nrows
			
			allsqls = ""
			keys = ["total_users", "today_topics", "yesterday_topics", \
				"total_topics", "total_comments"];
			values = [total_users, today_topics, yesterday_topics,
				total_topics, total_comments];
				
			for i in range(0, len(keys)):
				sql = ("UPDATE `stb_site_stats` SET " + \
					"`value`=%d, `update_time`=%d " + \
					"WHERE `item`=\"%s\";\n") % \
					(values[i], tsnow, keys[i]);
				allsqls += sql;
			
			ntc = dict() # Node Topic Count
			for m in db_messages:
				nid = m.node_id
				if nid == -999:
					assert m.is_reply
					continue
				else:
					if not ntc.has_key(nid):
						ntc[nid] = 0
					ntc[nid] += 1
			sql += "UPDATE stb_nodes SET listnum=CASE "
			for k, v in ntc.items():
				sql = sql + "WHEN node_id=%d THEN %d " % (k, v)
			sql = sql + "ELSE 0 END;\n"
			allsqls += sql
			
			db_messages = sorted(db_messages, key = lambda x : x.last_reply_time, reverse = False)
			
			order = 0
			sql = "UPDATE stb_topics SET ord = CASE "
			for m in db_messages:
				if m.is_reply == False:
					m.order = order;
					order += 1;
					sql = sql + "WHEN topic_id = %d THEN %d " % (m.primary_key, m.order)
			sql = sql + "ELSE ord END" 
			allsqls += sql
			
			# Notifications here
			computed_notifs = []
			diff_set = []
			hashes2 = set([])
			user_to_numnew = dict()
			
			# 最近更新时间
			sql = "\nUPDATE stb_site_stats SET update_time=%d WHERE item='mail_update_time';\n" % \
				int(time.time())
			allsqls += sql
			
			for n in db_notifications:
				hashes2.add(n.getHash())
				
			for m in db_messages:
				if m.is_reply == False:
					for c in m.children:
						n = analyze.Notification(-999, m, c.sender, m.sender, 1, c.date)
						computed_notifs.append(n)
						if not n.getHash() in hashes2:
							diff_set.append(n)
			
			print "%d db_messages" % len(db_messages)
			print "Has %d, computed %d, need to add %d notifications" % ( \
				len(db_notifications), len(computed_notifs), len(diff_set))
			
			if len(diff_set) > 0:
				allsqls = allsqls + "\n"
				nid = max_notification_id
				for n in diff_set:
					nid = nid + 1
					n.nid = nid
					allsqls += n.toSQL() + "\n"
					
				for n in computed_notifs:
					to_email = n.to_user.email
					u = db_email_to_user[to_email]
					if n.ntype != 0:
						if not user_to_numnew.has_key(u):
							user_to_numnew[u] = 0
						user_to_numnew[u] += 1
						
				if len(user_to_numnew) > 0:
					allsqls += "UPDATE `stb_users` SET notices = CASE "
					for u, n in user_to_numnew.items():
						allsqls += "WHEN uid=%d THEN %d " % (u.uid, n)
					allsqls += "ELSE notices END;\n"	
			
			WriteToDBNoGUI(allsqls, readdb_args)
			print "Done!"
			exit(0)
			
		else:
			print "Ah! Please enter a valid action for non-GUI mode."
			exit(0)
		
	LoadLastSave();
	g_my_app = QtGui.QApplication(sys.argv)
	g_w = MyApp()
	g_w.show()
	g_w.setInitDate()
	rtc = g_my_app.exec_()
	SaveLastSave();
	print "Ho!"
	sys.exit(rtc)
