/*
 * PEModule.java - This file is part of the Jakstab project.
 * 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 * Copyright (C) 2003 The University of Arizona
 *
 * The original code for this class was taken from "MBEL: The Microsoft 
 * Bytecode Engineering Library" and modified for use with Jakstab.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */

package org.jakstab.loader.pe;

import java.io.*;
import java.util.*;

import org.jakstab.Options;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.*;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.SymbolFinder;
import org.jakstab.loader.*;
import org.jakstab.loader.UnresolvedSymbol.AddressingType;

/** 
 * This class is used to parse and hold a PE/COFF file.
 * 
 * @author Michael Stepp, Johannes Kinder
 */
public class PEModule extends AbstractCOFFModule {
	
	private final static Logger logger = Logger.getLogger(PEModule.class);

	private MSDOS_Stub msdos_stub;
	private PE_Header pe_header;
	private ExportEntry[] exportEntries;
	private Map<AbsoluteAddress, Pair<String, String>> importTable;
	private String fileName; 
	private final PESymbolFinder symbolFinder;
	
	/**
	 * Parses a PEModule from a specified file
	 */
	public PEModule(File peFile, Architecture arch) throws IOException, BinaryParseException {

		InputStream inStream = new FileInputStream(peFile);
		fileName = peFile.getName();
		
		inBuf = new BinaryFileInputBuffer(inStream);

		msdos_stub = new MSDOS_Stub(inBuf);

		// Verify PE signature ///////////
		inBuf.seek(msdos_stub.getHeaderAddress());
		if (!inBuf.match(PE_Header.PE_TAG))
			throw new BinaryParseException("PEModule: Missing PE signature");
		//////////////////////////////////

		coff_header = new COFF_Header(inBuf);
		pe_header   = new PE_Header(inBuf);

		///// Parse Section Headers and sections /////////////////////////
		section_headers = new SectionHeader[coff_header.getNumberOfSections()];
		for (int i=0;i<coff_header.getNumberOfSections();i++){
			section_headers[i] = new SectionHeader(inBuf);
		}
		/////////////////////////////////////////////////////////////////

		/////////////////////////////////////////////////////////////////
		// Parse exports and build export table
		long expTableRVA =
			pe_header.getDataDirectory()[ImageDataDirectory.EXPORT_TABLE_INDEX].VirtualAddress;
		if (expTableRVA > 0) { // We have an export table
			logger.debug("-- Reading export table...");
			inBuf.seek(getFilePointerFromRVA(expTableRVA));
			ImageExportDirectory imageExportDirectory = new ImageExportDirectory(inBuf);

			inBuf.seek(getFilePointerFromRVA(imageExportDirectory.AddressOfFunctions));
			// Parse EAT
			ExportEntry[] tmpEntries = 
				new ExportEntry[(int)imageExportDirectory.NumberOfFunctions];
			int eatEntries = 0;
			for (int i = 0; i < tmpEntries.length; i++) {
				long rva = inBuf.readDWORD();
				if (rva > 0) {
					tmpEntries[i] = new ExportEntry((int)(i + imageExportDirectory.Base), 
							new AbsoluteAddress(rva + getBaseAddress()));
					eatEntries++;
				}
			}
			
			long namePtr = getFilePointerFromRVA(imageExportDirectory.AddressOfNames);
			long ordPtr = getFilePointerFromRVA(imageExportDirectory.AddressOfNameOrdinals);
			for (int i = 0; i < imageExportDirectory.NumberOfNames; i++) {
				// read next ENT entry
				inBuf.seek(namePtr);
				long rva = inBuf.readDWORD();
				namePtr = inBuf.getCurrent();
				// read export name
				inBuf.seek(getFilePointerFromRVA(rva));
				String expName = inBuf.readASCII();
				// read next EOT entry
				inBuf.seek(ordPtr);
				int ord = inBuf.readWORD();
				ordPtr = inBuf.getCurrent();
				tmpEntries[ord].setName(expName);
			}
			exportEntries = new ExportEntry[eatEntries];
			int j = 0;
			for (int i = 0; i < tmpEntries.length; i++)
				if (tmpEntries[i] != null) exportEntries[j++] = tmpEntries[i];
			logger.debug("-- Got " + exportEntries.length + " exported symbols.");
		} else logger.debug("-- File contains no exports");
		
		
		/////////////////////////////////////////////////////////////////
		// Parse imports and build import table
		importTable = new HashMap<AbsoluteAddress, Pair<String,String>>();
		long impTableRVA = 
			pe_header.getDataDirectory()[ImageDataDirectory.IMPORT_TABLE_INDEX].VirtualAddress;
		if (impTableRVA > 0) { // We have an import table
			logger.debug("-- Reading image import descriptors...");
			inBuf.seek(getFilePointerFromRVA(impTableRVA));
			List<ImageImportDescriptor> imageImportDescriptors = 
				new LinkedList<ImageImportDescriptor>();
			while(true) {
				ImageImportDescriptor cur = new ImageImportDescriptor(inBuf);
				if (cur.isZero()) break;
				imageImportDescriptors.add(cur);
			}

			for (ImageImportDescriptor descriptor : imageImportDescriptors) {
				inBuf.seek(getFilePointerFromRVA(descriptor.Name));
				String libraryFileName = inBuf.readASCII();
				logger.debug("-- Parsing imports from " + libraryFileName + "...");
				// Normalize filenames to lower case
				libraryFileName = libraryFileName.toLowerCase();

				// Check if the library is bound.
				boolean bound = descriptor.TimeDateStamp != 0;

				/* Read Import Address Table or Import Name Table */
				long iatFilePtr;
				if (bound) iatFilePtr = getFilePointerFromRVA(descriptor.OriginalFirstThunk);
				else iatFilePtr = getFilePointerFromRVA(descriptor.FirstThunk);
				// import names will be associated to IAT addresses in any case
				//AbsoluteAddress iatAddress = (new RVAPointer(this, descriptor.FirstThunk)).getVAPointer();
				AbsoluteAddress iatAddress = new AbsoluteAddress(descriptor.FirstThunk + getBaseAddress());

				while(true) {
					inBuf.seek(iatFilePtr);
					long thunk = inBuf.readDWORD();
					iatFilePtr = inBuf.getCurrent(); // Save buffer position
					if (thunk == 0) break;
					if ((thunk & 0x80000000) != 0) {
						/* Thunk contains ordinal value in low 31 bits. 
						 * (for 64 bit files this would be the lower 63 bits.  */
						int ord = (int) (thunk & 0x7FFFFFFF);
						String ordName = "ord(" + ord + ")";
						importTable.put(iatAddress,  Pair.create(libraryFileName, ordName));
					} else {
						/* Thunk contains an RVA of either a IMAGE_IMPORT_BY_NAME 
						 * structure [word (ord hint) , string (function name)]
						 * or to a forwarder string. Forwarding not supported at 
						 * the moment!*/

						long rva = getFilePointerFromRVA(thunk);
						if (rva < 0) 
							throw new BinaryParseException("RVA in thunk points outside of image!");
						// Just skip the ord hint (WORD), we don't need it.
						inBuf.seek(rva + 2);
						String funcName = inBuf.readASCII();
						importTable.put(iatAddress, Pair.create(libraryFileName, funcName));
					}
					// Advance IAT entry by one DWORD
					iatAddress = new AbsoluteAddress(iatAddress.getValue() + 4);
				}
			}
		}
		
		
		// TODO: Parse delayload imports
		
		logger.debug("-- Got " + importTable.size() + " imported function symbols.");
				
		symbolFinder = new PESymbolFinder(this);
	}

	public Map<AbsoluteAddress, Pair<String, String>> getImportTable() {
		return importTable;
	}

	public int getNumberOfExports() {
		if (exportEntries != null)
			return exportEntries.length;
		else return 0;
	}

	public ExportEntry getExport(int num) {
		return exportEntries[num];
	}

	@Override
	public AbsoluteAddress getEntryPoint() {
		return new AbsoluteAddress(getBaseAddress() + pe_header.getAddressOfEntryPoint());
	}

	@Override
	public boolean isReadOnly(AbsoluteAddress a) {
		int section = getSectionNumber(a);
		if (section >= 0) {
			return getSectionHeader(section).isReadOnlySection();
		}
		else { 
			return false;
		}
	}
	
	public String getFileName() {
		return fileName;
	}
	
	@Override
	public SymbolFinder getSymbolFinder() {
		return symbolFinder;
	}

	@Override
	protected final long getBaseAddress() {
		return pe_header.getImageBase();
	}

	@Override
	protected final int getSectionNumberByRVA(long rva) {
		if (rva < 0) return -1;
		for (int i=0; i < getNumberOfSections(); i++)
			if (getSectionHeader(i).VirtualAddress <= rva && 
					(getSectionHeader(i).VirtualAddress + 
							getSectionHeader(i).SizeOfRawData) > rva)
				return i;
		return -1;
	}

	@Override
	public Set<UnresolvedSymbol> getUnresolvedSymbols() {
		Set<UnresolvedSymbol> unresolvedSymbols = new FastSet<UnresolvedSymbol>();
		for (Map.Entry<AbsoluteAddress, Pair<String, String>> importEntry : getImportTable().entrySet()) {
			AbsoluteAddress va = importEntry.getKey(); 
			String libraryName = importEntry.getValue().getLeft();
			String symbolName = importEntry.getValue().getRight();
			unresolvedSymbols.add(new UnresolvedSymbol(this, libraryName, symbolName, (int)getFilePointer(va), AddressingType.ABSOLUTE));
		}
		
		return unresolvedSymbols;
	}

	@Override
	public Set<ExportedSymbol> getExportedSymbols() {
		Set<ExportedSymbol> exportedSymbols = new FastSet<ExportedSymbol>();
		
		if (Options.wdm.getValue() && fileName.endsWith(".sys")) {
			//FIXME: adds multiple DriverEntries for multiple PE modules, and is generally hackish
			logger.debug("Exporting DriverEntry at " + getEntryPoint());
			exportedSymbols.add(new ExportedSymbol(this, "_DriverEntry@8", getEntryPoint()));
		} else {
			exportedSymbols.add(new ExportedSymbol(this, "start", getEntryPoint()));
		}
		
		if (exportEntries != null) for (ExportEntry ee : exportEntries) {
			String name = ee.getName();
			if (name == null) name = "ord(" + ee.getOrdinal() + ")";
			exportedSymbols.add(new ExportedSymbol(this, name, ee.getAddress()));
		}
		return exportedSymbols;
	}

}
